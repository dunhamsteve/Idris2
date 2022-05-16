module Compiler.ES.SourceMap

import Compiler.ES.Doc
import Libraries.Data.SortedMap
import Protocol.Hex
import Data.Bits
import Data.List
import Data.SnocList
import Data.String
import Data.Vect
import Core.FC
import Core.Name.Namespace
import Control.Monad.State

record SourceMap where
    constructor MkSourceMap
    -- verison: 3
    -- names: []
    -- file: String
    sourceIx : Int
    sources: SortedMap String Int
    -- these get concatenated at the end
    pos : FilePos
    mappings: SnocList Char

    prev : Vect 4 Int
    line : Maybe Int




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
                go (shiftR n 5)
            else do
                let ch = base64 (n .&. 31)
                pushChar ch

start : SourceMap
start = MkSourceMap 0 empty (0,0) Lin [0,0,0,0] Nothing

-- We need a small test case

-- Convert an Idris2 string to a JSON String
-- by escaping most non-alphanumeric characters.
-- Adapted from Compiler.ES.Codegen.jsString
jsonString : String -> Doc
jsonString s = Text $ "\"" ++ (concatMap okchar (unpack s)) ++ "\""
  where
    okchar : Char -> String
    okchar c = if (c >= ' ') && (c /= '\\')
                  && (c /= '"') && (c /= '\'') && (c <= '~')
                  then cast c
                  else case c of
                            '\0' => "\\0"
                            '\'' => "\\'"
                            '"' => "\\\""
                            '\r' => "\\r"
                            '\n' => "\\n"
                            other => "\\u{" ++ asHex (cast c) ++ "}"

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
    map fst $ sortBy (\(_,a),(_,b) => compare a b) $ SortedMap.toList smap.sources

showJSON : SourceMap -> String -> Doc
showJSON smap filename =
    object [
        ("version", "3"),
        ("names", "[]"),
        ("file", jsonString filename),
        ("sources", array (map jsonString $ sourceList smap)),
        ("mappings", jsonString $ fastPack $ smap.mappings <>> [])
    ]

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

Semigroup FilePos where
    (l,c) <+> (0,c')  = (l, c + c')
    (l,c) <+> (l',c') = (l + l', c')

addPos : FilePos -> State SourceMap ()
addPos p = modify { pos $= (<+> p) }

fileNum : String -> State SourceMap Int
fileNum fn = ST $ \st => case lookup fn st.sources of
    Nothing =>
        let st' = { sources $= (insert fn st.sourceIx), sourceIx $= (+1) } st
        in pure (st', st.sourceIx)
    (Just x) => pure (st,x)

addMark : String -> FilePos -> State SourceMap ()
addMark fn (srcLine, srcCol) = do
    ix <- fileNum fn
    st <- get
    let (destLine, destCol) = st.pos
        skip = destLine - (fromMaybe 0 st.line)

    when (Just destLine == st.line) (pushChar ',')
    when (skip > 0) $ traverse_ pushChar $ List.replicate (cast skip) ';'

    -- emit st.pos.fst - st.line semicolons
    -- or a comma if st.line == Just st.pos.fst
    let [destCol', ix', srcLine', srcCol'] = st.prev
    if skip > 0 then encode (destCol + 1) else encode (destCol - destCol')
    encode $ ix - ix'
    encode $ srcLine - srcLine'
    encode $ srcCol + 1  - srcCol'

    let next = the (Vect 4 Int) [destCol, ix, srcLine, srcCol]
    modify { prev := next, line := Just destLine }




-- REVIEW maybe change State SourceMap () to a Core thinger
-- It's just a Ref, maybe even more complex than State which
-- is contained in prettyMap

-- REVIEW do we want to mark none for unknown?
emit : FC -> State SourceMap ()
emit (MkFC d s e) = case d of
    (PhysicalIdrSrc mod) => addMark (toPath mod ++ ".idr") s
    (PhysicalPkgSrc fname) => addMark fname s
    (Virtual ident) => modify id
emit (MkVirtualFC d s e) = case d of
    (PhysicalIdrSrc mod) => addMark (toPath mod ++ ".idr") s
    (PhysicalPkgSrc fname) => addMark fname s
    (Virtual ident) => modify id
emit EmptyFC = modify id


||| like pretty, but build a sourceMap
||| FIXME I'm not super happy with this because it needs
||| to match the behavior of pretty to be correct.
export
prettyMap : Doc -> String -> String
prettyMap doc fn =
    pretty $ showJSON (execState start $ go 0 doc) fn
    where
        go : (spaces : Nat) -> Doc -> State SourceMap ()
        go n [] = pure ()
        go n LineBreak = addPos (1,0)
        go n SoftSpace = addPos (0,1)
        go n (Text x) = addPos (0, strLength x)
        go n (Nest k x) = go (n+k) x
        go n (Seq x y) = go n x >> go n y
        go n (Ann fc x) = emit fc >> go n x

