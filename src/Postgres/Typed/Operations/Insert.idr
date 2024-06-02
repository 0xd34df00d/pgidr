module Postgres.Typed.Operations.Insert

import Control.Monad.State

import Data.String
import Data.Vect
import Data.Vect.Quantifiers
import Data.Vect.Quantifiers.Extra

import Postgres.C

import public Postgres.Typed.Tuple

import Postgres.Typed.Operations.Class
import Postgres.Typed.Operations.Helpers
import public Postgres.Typed.Operations.Expression
import public Postgres.Typed.Operations.Returning

%default total
%prefix_record_projections off

record InsertColumn where
  constructor MkIC
  colName : String
  value : String

mkInsertQuery : {k, tbl : _} ->
                (cols : Vect k InsertColumn) ->
                (returning : Columns OneRow tbl ret) ->
                String
mkInsertQuery cols returning =
  let namesStr = joinBy ", " $ toList $ .colName <$> cols
      placeholders = joinBy ", "
                   $ toList
                   $ tabulate {len = k} (\i => "$" ++ show (finToNat i + 1))
      returningClause = mkReturningClause returning
   in "INSERT INTO \{tbl.name} (\{namesStr}) VALUES (\{placeholders}) \{returningClause}"

mkInsertColumns : (tbl : Table n) ->
                  (val : Tuple tbl.signature Write) ->
                  (k ** Vect k InsertColumn)
mkInsertColumns t = catMaybes
                  . forget
                  . mapPropertyRelevant (\se => onSigValUniform (MkIC se.name.uname . toTextual) se)

public export
record Insert (tbl : Table ncols) (ret : Type) where
  constructor MkInsert
  value : Tuple tbl.signature Write
  returning : Columns OneRow tbl ret

-- TODO consider indexing `Expr` with its length in its type
-- to have static guarantees about whether the result is long enough
extractExprResult : MonadError ExecError m =>
                    Result s ->
                    Expr tbl ret ->
                    m ret
extractExprResult res = evalStateT 0 . go
  where
  shift : Nat -> StateT Nat m ret' -> StateT Nat m ret'
  shift n act = do
    res <- act
    modify (+ n) $> res

  go : Expr tbl' ret' ->
       StateT Nat m ret'
  go (EConst val) = shift 1 $ pure $ valueOf val
  go ENone = pure ()
  go (EAll {n}) = shift n $ ?rhs_1
  go (EColumn sig ix) = shift 1 $ ?rhs_2
  go (EList exprs) = go' exprs
    where
    go' : {0 tys : Vect n Type} ->
          (exprs : All (Expr baseTy) tys) ->
          StateT Nat m (HVect tys)
    go' [] = pure []
    go' (expr :: exprs) = [| go expr :: go' exprs |]
  go (EBinRel _ _ _) = shift 1 $ ?rhs_4
  go (ENot _) = shift 1 $ ?rhs_5

execInsert : {tbl : _} -> Insert tbl ret -> ExecuteFun ret
execInsert (MkInsert val returning) = do
  let (_ ** cols) = mkInsertColumns tbl val
      query = mkInsertQuery cols returning
      params = map (.value) cols
  QueryResult result <- execQueryParams query params
  ensureQuerySuccess query result
  extractReturning result returning

insertBase : (0 tbl : Table n) ->
             (val : Tuple tbl.signature Write) ->
             Insert tbl ()
insertBase _ val = MkInsert val CNone

insertOp : {tbl : _} ->
           Insert tbl ret ->
           Operation ret
insertOp = singleOp . execInsert

data DInto : Type where
public export
into : Dummy DInto
into = MkDF

export
insert : (0 _ : Dummy DInto) ->
         {n : _} ->
         (tbl : Table n) ->
         (val : Tuple tbl.signature Write) ->
         Operation ()
insert _ tbl = insertOp . insertBase tbl

export
insert' : (0 _ : Dummy DInto) ->
          {n : _} ->
          (tbl : Table n) ->
          (val : Tuple tbl.signature Write) ->
          (Insert tbl () -> Insert tbl ret) ->
          Operation ret
insert' _ tbl val f = insertOp $ f (insertBase tbl val)
