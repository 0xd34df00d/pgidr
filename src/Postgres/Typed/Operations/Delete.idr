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
record Delete (tbl : Table n) ret where
  constructor MkDelete
  table : String
  where' : Expr tbl.signature Bool
  returning : Columns ManyRows tbl ret

execDelete : Delete tbl ret -> ExecuteFun ret
execDelete (MkDelete table where' returning) = do
  let query = "DELETE FROM \{table} " ++
              "WHERE \{toQueryPart where'} " ++
              mkReturningClause returning
  QueryResult result <- execQuery query
  ensureQuerySuccess query result
  extractReturning result returning

export
delete : (0 _ : Dummy DFrom) ->
         {n : _} ->
         (tbl : Table n) ->
         Expr tbl.signature Bool ->
         Operation ()
delete _ tbl expr = singleOp $ execDelete $ MkDelete tbl.name expr CNone

export
delete' : (0 _ : Dummy DFrom) ->
          {n : _} ->
          (tbl : Table n) ->
          Expr tbl.signature Bool ->
          (Delete tbl () -> Delete tbl ret) ->
          Operation ret
delete' _ tbl expr f = singleOp $ execDelete $ f $ MkDelete tbl.name expr CNone
