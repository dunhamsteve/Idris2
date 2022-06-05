module Compiler.ES.SourceMap

-- I've found https://sokra.github.io/source-map-visualization/#custom helpful for visualizing results.

import Compiler.ES.Doc
import Libraries.Data.SortedMap
import Libraries.Utils.Path
import Protocol.Hex
import Data.Bits
-- A compiler used by the quickcheck build seems to need this
import Data.DPair
import Data.List
import Data.SnocList
import Data.String
import Data.Vect
import Core.Context
import Core.Directory
import Core.FC
import Core.Name.Namespace
import Core.Options
import Control.Monad.State

export
record SourceMap where
    constructor MkSourceMap
    segments : SnocList String
    sourceIx : Int
    sourceMap: SortedMap ModuleIdent Int
    -- these get concatenated at the end
    pos : FilePos
    mappings: SnocList Char

    prev : Vect 4 Int
    line : Maybe Int

start : SourceMap
start = MkSourceMap Lin 0 empty (0,0) Lin [0,0,0,0] Nothing


pushChar : Char -> State SourceMap ()
pushChar ch = modify { mappings $= (:< ch) }

||| Add a base64 VLQ signed integer to the source map
encode : Int -> State SourceMap ()
encode n = if n < 0 then go ((0-n)*2 + 1) else go (n*2)
    where
        base64 : Int -> Char
        base64 n =
            if      n < 26 then chr $ n + 65
            else if n < 52 then chr $ n + 97 - 26
            else if n < 62 then chr $ n + 48 - 52
            else if n == 62 then '+'
            else '/'

        go : Int -> State SourceMap ()
        go n = if n > 31
            then do
                let ch = base64 (n .&. 31 .|. 32)
                pushChar ch
                go (n `div` 32)
            else do
                let ch = base64 (n .&. 31)
                pushChar ch

-- Convert an Idris2 string to a JSON String
-- by escaping most non-alphanumeric characters.
-- Adapted from Compiler.ES.Codegen.jsString
jsonString : String -> Doc
jsonString s = Text $ "\"" ++ (concatMap okchar (unpack s)) ++ "\""
  where
    okchar : Char -> String
    okchar c = if (c >= ' ') && (c /= '\\')
                  && (c /= '"') && (c <= '~')
                  then cast c
                  else case c of
                            '\0' => "\\0"
                            '"' => "\\\""
                            '\r' => "\\r"
                            '\n' => "\\n"
                            '\\' => "\\\\"
                            other => "\\u" ++ leftPad '0' 4 (asHex $ cast c)

field : (String, Doc) -> Doc
field (key, value) = jsonString key <+> softColon <+> value

applyList : (lparen : Doc) -> (rparen : Doc) -> (sep : Doc) -> List Doc -> Doc
applyList l r sep ds = l <+> (concat $ intersperse sep ds) <+> r

object : (args : List (String,Doc)) -> Doc
object = applyList "{" "}" softComma . map field

array : List Doc -> Doc
array = applyList "[" "]" softComma

sourceList : SourceMap -> List String
sourceList smap =
    map (\x => toPath (fst x) ++ ".idr") $ sortBy (\(_,a),(_,b) => compare a b) $ SortedMap.toList smap.sourceMap

-- "lines" loses the trailing newlines, but that should be ok for us
||| Turn a file into an annotated Doc to enable
||| sourcemap generation.
export
fileToDoc : String -> String -> Doc
fileToDoc fn text = go 0 (lines text)
    where
        fc : Int -> FC
        fc n = MkFC (PhysicalPkgSrc fn) (n,0) (n+1,0)
        go : Int -> List String -> Doc
        go n [] = []
        go n (x :: xs) = Seq (Ann (fc n) (Text x)) (go (n+1) xs)

(<++>) : FilePos -> FilePos -> FilePos
(l,c) <++> (0,c')  = (l, c + c')
(l,c) <++> (l',c') = (l + l', c')


||| Add a file to the list of sources if necessary and return its index
fileNum : ModuleIdent -> State SourceMap Int
fileNum fn = ST $ \st => case lookup fn st.sourceMap of
    Nothing =>
        let ix = st.sourceIx
            st' = { sourceMap $= (insert fn ix), sourceIx := (ix+1) } st
        in pure (st', ix)
    (Just x) => pure (st,x)

||| Add a mark for filePos to mappings and update the state.
addMark : ModuleIdent -> FilePos -> State SourceMap ()
addMark fn (srcLine, srcCol) = do
    ix <- fileNum fn
    st <- get
    let (destLine, destCol) = st.pos
        skip = destLine - (fromMaybe 0 st.line)

    -- Marks on the same line are separated by ,
    when (Just destLine == st.line) (pushChar ',')

-- Lines are separated by ;
    when (skip > 0) $ traverse_ pushChar $ List.replicate (cast skip) ';'

    let [destCol', ix', srcLine', srcCol'] = st.prev

    -- column in output javascript is delta encoded, but reset on new line
    if skip > 0 then encode destCol else encode (destCol - destCol')

    let next : Vect 4 Int = [destCol, ix, srcLine, srcCol]

    -- skip if same as previous
    if skip == 0 && next == st.prev then pure ()
        else do
            -- otherwise delta-encode
            encode $ ix - ix'
            encode $ srcLine - srcLine'
            encode $ srcCol - srcCol'
            modify { prev := next, line := Just destLine }

-- REVIEW maybe change State SourceMap () to a Core thinger
-- It's just a Ref, maybe even more complex than State which
-- is contained in prettyMap

||| Emit a source reference for the current output position
emit : FC -> State SourceMap ()
emit (MkFC (PhysicalIdrSrc mod) s e) = addMark mod s
-- REVIEW whether these are wanted in sourcemap
-- emit (MkVirtualFC (PhysicalIdrSrc mod) s e) = addMark mod s
emit _ = pure ()


try : Core a -> Core (Maybe a)
try x = catch (Just <$> x) (const $ pure Nothing)

||| Read the source of a module (logic adapted from idris2-lsp mkLocation')
readSource : Ref Ctxt Defs => ModuleIdent -> Core (String, Maybe String)
readSource mi = do
    defs <- get Ctxt
    let pkg_dirs = filter (/= ".") defs.options.dirs.extra_dirs

    source <- catch (Just <$> (nsToSource EmptyFC mi >>= readFile))
        (const $ do
            defs <- get Ctxt
            let pkg_dirs = filter (/= ".") defs.options.dirs.extra_dirs
                candidates = map (</> toPath mi <.> "idr") pkg_dirs
            Just cand <- firstAvailable candidates | _ => pure Nothing
            Just <$> readFile cand)

    when (isNothing source) (coreLift $ putStrLn "miss \{show mi}")
    pure (toPath mi ++ ".idr", source)

listMods : SourceMap -> List ModuleIdent
listMods smap = map fst $ sortBy (\(_,a),(_,b) => compare a b) $ SortedMap.toList smap.sourceMap

maybeJsonString : Maybe String -> Doc
maybeJsonString Nothing = Text "null"
maybeJsonString (Just x) = jsonString x

export
showJSON : Ref Ctxt Defs => SourceMap -> String -> Core String
showJSON smap filename = do
    sourceInfo <- traverse readSource $ listMods smap
    -- pure $ { sources := map fst foo, sourcesContent := map snd foo} smap
    d <- getDirs
    -- coreLift $ printLn d

    pure $ pretty $ object [
        ("version", "3"),
        ("names", "[]"),
        ("file", jsonString filename),
        ("sources", array $ map (jsonString . fst) sourceInfo),
        ("sourcesContent", array $ map (maybeJsonString . snd) sourceInfo),
        ("mappings", jsonString $ fastPack $ smap.mappings <>> [])
    ]


export
showJavascript : SourceMap -> String -> String
showJavascript smap fn = fastConcat $ smap.segments <>> ["\n//# SourceMappingURL=", fn, ".map\n"]

addPos : FilePos -> State SourceMap ()
addPos p = modify { pos $= (<++> p) }

nSpaces : Nat -> String
nSpaces n = fastPack $ replicate n ' '

addText : String -> State SourceMap ()
addText s = modify { pos $= (<++> (0,strLength s)), segments $= (:< s)}

addNewLine : Nat -> State SourceMap ()
addNewLine n = let text : String = "\n" ++ nSpaces n in
    modify { pos $= (<++> (1,cast n)), segments $= (:< text) }

||| debugFC is used to inject FC comments when debugging
||| the sourcemap generation
debugFC : FC -> State SourceMap ()
debugFC fc = do
    addText " /*"
    case fc of
        (MkVirtualFC _ _ _) => addText "V:"
        _ => pure ()
    addText (show fc)
    addText "*/"

export
compactMap :  Ref Ctxt Defs => Doc -> SourceMap
compactMap doc =
    execState start $ go doc
    where
        go : Doc -> State SourceMap ()
        go Nil        = pure ()
        go LineBreak  = pure ()
        go SoftSpace  = pure ()
        go (Text x)   = addText x
        go (Nest k x) = go x
        go (Seq x y)  = go x >> go y
        go (Ann fc x) = do
            -- debugFC fc
            emit fc
            go x

||| like pretty, but build a sourceMap
||| FIXME I'm not super happy with this because it needs
||| to match the behavior of pretty to be correct.
export
prettyMap : Ref Ctxt Defs => Doc -> SourceMap
prettyMap doc =
    execState start $ go 0 doc
    where
        go : (spaces : Nat) -> Doc -> State SourceMap ()
        go n Nil        = pure ()
        go n LineBreak  = addNewLine n
        go n SoftSpace  = addText " "
        go n (Text x)   = addText x
        go n (Nest k x) = go (n+k) x
        go n (Seq x y)  = go n x >> go n y
        -- go n (Ann fc x) = emit fc >> go n x
        go n (Ann fc x) = do
            -- debugFC fc
            emit fc
            go n x
