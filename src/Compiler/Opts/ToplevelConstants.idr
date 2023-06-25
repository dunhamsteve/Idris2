module Compiler.Opts.ToplevelConstants

import Core.CompileExpr
import Core.Context
import Core.Name
import Core.TT

import Data.List1
import Data.Vect
import Libraries.Data.Graph
import Libraries.Data.SortedSet
import Libraries.Data.SortedMap

--------------------------------------------------------------------------------
--          Call Graph
--------------------------------------------------------------------------------

-- direct calls from a top-level function's expression to other
-- top-level functions.
0 CallGraph : Type
CallGraph = SortedMap Name (SortedSet Name)

-- top-level functions called by an expression
calls : NamedCExp -> SortedSet Name
calls (NmLocal fc p) = empty
calls (NmRef fc n1) = singleton n1
calls (NmLam fc x y) = calls y
calls (NmLet fc x z w) = calls w <+> calls z
calls (NmApp fc x xs) = calls x <+> concatMap calls xs
calls (NmCon fc n1 x tag xs) = concatMap calls xs
calls (NmOp fc f xs) = concatMap calls xs
calls (NmExtPrim fc p xs) = concatMap calls xs
calls (NmForce fc lz x) = calls x
calls (NmDelay fc lz x) = calls x
calls (NmConCase fc sc xs x) =
  calls sc <+>
  concatMap (\(MkNConAlt _ _ _ _ y) => calls y) xs <+>
  concatMap calls x
calls (NmConstCase fc sc xs x) =
  calls sc <+>
  concatMap (\(MkNConstAlt _ y) => calls y) xs <+>
  concatMap calls x
calls (NmPrimVal fc cst) = empty
calls (NmErased fc) = empty
calls (NmCrash fc str) = empty

defCalls : NamedDef -> SortedSet Name
defCalls (MkNmFun args x) = calls x
defCalls (MkNmCon tag arity nt) = empty
defCalls (MkNmForeign ccs fargs x) = empty
defCalls (MkNmError x) = calls x

callGraph : List (Name, FC, NamedDef) -> CallGraph
callGraph = fromList . map (\(n,_,d) => (n, defCalls d))

isRecursive : CallGraph -> List1 Name -> Bool
isRecursive g (x ::: Nil) = maybe False (contains x) $ lookup x g
isRecursive _ _           = True

recursiveFunctions : CallGraph -> SortedSet Name
recursiveFunctions graph =
  let groups := filter (isRecursive graph) $ tarjan graph
   in concatMap (SortedSet.fromList . forget) groups

defFails : SortedSet Name -> NamedDef -> Bool
defFails ns (MkNmFun args x) = fails x
  where
    fails : NamedCExp -> Bool
    fails (NmLocal fc n) = False
    fails (NmRef fc n) = contains n ns
    fails (NmLam fc x y) = fails y
    fails (NmLet fc x y z) = fails y || fails z
    fails (NmApp fc x xs) = any fails (x :: xs)
    fails (NmCon fc n x tag xs) = any fails xs
    fails (NmOp fc f xs) = any fails xs
    fails (NmExtPrim fc p xs) = any fails xs
    fails (NmForce fc lz x) = fails x
    fails (NmDelay fc lz x) = fails x
    fails (NmConCase fc sc xs x) = fails sc
      || any (\(MkNConAlt _ _ _ _ y) => fails y) xs
      || fromMaybe False (fails <$> x)
    fails (NmConstCase fc sc xs x) = fails sc
      || any (\(MkNConstAlt _ y) => fails y) xs
      || fromMaybe False (fails <$> x)
    fails (NmPrimVal fc cst) = False
    fails (NmErased fc) = False
    fails (NmCrash fc str) = str == "No clauses"
defFails ns (MkNmCon tag arity nt) = False
defFails ns (MkNmForeign ccs fargs x) = False
defFails ns (MkNmError x) = True

--------------------------------------------------------------------------------
--          Sorting Functions
--------------------------------------------------------------------------------

data SortTag : Type where

record SortST where
  constructor SST
  processed : SortedSet Name
  fails     : SortedSet Name
  triples   : SnocList (Name, FC, NamedDef)
  map       : SortedMap Name (Name, FC, NamedDef)
  graph     : CallGraph

checkFails : Ref SortTag SortST => (Name, FC, NamedDef) -> Core ()
checkFails (n, _, def) = do
  st <- get SortTag
  when (defFails (fails st) def) $
    put SortTag $ { fails $= insert n } st

appendDef : Ref SortTag SortST => (Name, FC, NamedDef) -> Core ()
appendDef t = do
  st <- get SortTag
  put SortTag $ {triples $= (:< t)} st

getCalls : Ref SortTag SortST => Name -> Core (List Name)
getCalls n = map (maybe [] SortedSet.toList . lookup n . graph) (get SortTag)

getTriple : Ref SortTag SortST => Name -> Core (Maybe (Name,FC,NamedDef))
getTriple n = map (lookup n . map) (get SortTag)

markProcessed : Ref SortTag SortST => Name -> Core ()
markProcessed n = do
  st <- get SortTag
  put SortTag $ {processed $= insert n} st

isProcessed : Ref SortTag SortST => Name -> Core Bool
isProcessed n = map (contains n . processed) (get SortTag)

sortDef : Ref SortTag SortST => Name -> Core ()
sortDef n = do
  False  <- isProcessed n | True => pure ()
  markProcessed n
  cs     <- getCalls n
  traverse_ sortDef cs
  Just t <- getTriple n | Nothing => pure ()
  appendDef t
  checkFails t

isConstant : (recursiveFunctions : SortedSet Name) -> (Name,FC,NamedDef) -> Bool
isConstant rec (n, _, MkNmFun [] _) = not $ contains n rec
isConstant _   _                    = False

export
sortDefs : List (Name, FC, NamedDef) -> Core (List (Name, FC, NamedDef), SortedSet Name)
sortDefs ts =
  let graph  := callGraph ts
      rec    := recursiveFunctions graph
      consts := map fst $ filter (isConstant rec) ts
      init   := SST {
                    processed = empty
                  , fails  = empty
                  , triples   = Lin
                  , map       = fromList (map (\t => (fst t, t)) ts)
                  , graph     = graph
                  }
   in do
     s       <- newRef SortTag init
     traverse_ sortDef (map fst ts)
     st <- get SortTag
     let sorted = triples st <>> []
     let consts = filter (\n => not $ contains n (fails st)) consts
     pure (sorted, fromList consts)
