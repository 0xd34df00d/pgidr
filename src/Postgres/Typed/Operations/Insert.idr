module Postgres.Typed.Operations.Insert

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
extractReturning : MonadError ExecError m =>
                   Result s ->
                   Expr tbl ret ->
                   m ret
extractReturning res = snd . go 0
  where
  go : (col : Nat) ->
       Expr tbl' ret' ->
       (Nat, m ret')
  go col (EConst val) = (1 + col, pure $ valueOf val)
  go col ENone = (col, pure ())
  go col (EAll {n}) = (n + col, ?rhs_2)
  go col (EColumn sig ix) = (1 + col, ?rhs_1)
  go col (EList exprs) = go' col exprs
    where
    go' : {0 tys : Vect n Type} ->
          (col : Nat) ->
          (exprs : All (Expr baseTy) tys) ->
          (Nat, m (HVect tys))
    go' col [] = (col, pure [])
    go' col (expr :: exprs) =
      let (col', val) = go col expr
          (col'', vals) = go' col' exprs
      in (col'', [| val :: vals |])
  go col (EBinRel _ _ _) = (1 + col, ?rhs_4)
  go col (ENot _) = (1 + col, ?rhs_8)

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
