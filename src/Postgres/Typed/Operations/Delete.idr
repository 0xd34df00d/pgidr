module Postgres.Typed.Operations.Delete

import public Postgres.Typed.Tuple

import Postgres.C

import Postgres.Typed.Operations.Class
import public Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.Helpers
import public Postgres.Typed.Operations.Returning

%default total
%prefix_record_projections off

data DFrom : Type where
public export
from : Dummy DFrom
from = MkDF

public export
record Delete (ty : Dir -> Type) ret where
  constructor MkDelete
  {fieldsCount : Nat}
  {auto tyIsTuple : IsTupleLike Unqualified fieldsCount ty}
  table : String
  where' : Expr ty Bool
  returning : Columns ManyRows ty ret

execDelete : Delete ty ret -> ExecuteFun ret
execDelete (MkDelete table where' returning) = do
  let query = "DELETE FROM \{table} " ++
              "WHERE \{toQueryPart where'} " ++
              mkReturningClause returning
  QueryResult result <- execQuery query
  ensureQuerySuccess query result
  extractReturning result returning

export
delete : (0 _ : Dummy DFrom) ->
         (0 ty : Dir -> Type) ->
         {n : _} ->
         (IsTupleLike Unqualified n ty, HasTableName ty) =>
         Expr ty Bool ->
         Operation ()
delete _ ty expr = singleOp $ execDelete $ MkDelete (tableNameOf ty) expr CNone

export
delete' : (0 _ : Dummy DFrom) ->
          (0 ty : Dir -> Type) ->
          {n : _} ->
          (IsTupleLike Unqualified n ty, HasTableName ty) =>
          Expr ty Bool ->
          (Delete ty () -> Delete ty ret) ->
          Operation ret
delete' _ ty expr f = singleOp $ execDelete $ f $ MkDelete (tableNameOf ty) expr CNone
