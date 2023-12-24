module Postgres.Typed.Operations.Delete

import public Postgres.Typed.Tuple

import Postgres.C

import Postgres.Typed.Operations.Class
import public Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.Helpers

data DFrom : Type where
public export
from : Dummy DFrom
from = MkDF

public export
record Delete (ty : Dir -> Type) where
  constructor MkDelete
  table : String
  where' : Expr ty Bool

execDelete : Delete ty -> ExecuteFun ()
execDelete (MkDelete table where') conn = do
  let query = "DELETE FROM \{table} " ++
              "WHERE \{toQueryPart where'}"
  result <- execQuery conn query
  ensureQuerySuccess query result

export
delete : (0 _ : Dummy DFrom) ->
         (0 ty : Dir -> Type) ->
         (IsTupleLike Unqualified n ty, HasTableName ty) =>
         Expr ty Bool ->
         Operation ()
delete _ ty expr = singleOp $ execDelete $ MkDelete (tableNameOf ty) expr
