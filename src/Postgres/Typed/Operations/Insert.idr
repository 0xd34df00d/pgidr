module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect

import Data.Vect.Quantifiers.Extra

import Postgres.C

import public Postgres.Typed.Tuple

import Postgres.Typed.Operations.Class
import Postgres.Typed.Operations.Helpers
import public Postgres.Typed.Operations.Returning

%default total
%prefix_record_projections off

record InsertColumn where
  constructor MkIC
  colName : String
  value : String

mkInsertQuery : {k : _} ->
                (HasSignature Unqualified n ty, HasTableName ty) =>
                (cols : Vect k InsertColumn) ->
                (returning : Columns OneRow ty ret) ->
                String
mkInsertQuery cols returning =
  let namesStr = joinBy ", " $ toList $ .colName <$> cols
      placeholders = joinBy ", "
                   $ toList
                   $ tabulate {len = k} (\i => "$" ++ show (finToNat i + 1))
      returningClause = mkReturningClause returning
   in "INSERT INTO \{tableNameOf ty} (\{namesStr}) VALUES (\{placeholders}) \{returningClause}"

mkInsertColumns : IsTupleLike Unqualified n ty =>
                  (val : ty Write) ->
                  (k ** Vect k InsertColumn)
mkInsertColumns = catMaybes
                . forget
                . mapPropertyRelevant (\se => onSigValUniform (MkIC se.name.uname . toTextual) se)
                . toTuple

public export
record Insert (ty : Dir -> Type) (ret : Type) where
  constructor MkInsert
  {fieldsCount : Nat}
  {auto tyIsTuple : IsTupleLike Unqualified fieldsCount ty}
  {auto tyHasTable : HasTableName ty}
  value : ty Write
  returning : Columns OneRow ty ret

execInsert : Insert ty ret -> ExecuteFun ret
execInsert (MkInsert val returning) = do
  let (_ ** cols) = mkInsertColumns val
      query = mkInsertQuery {ty} cols returning
      params = map (.value) cols
  QueryResult result <- execQueryParams query params
  ensureQuerySuccess query result
  extractReturning result returning

insertBase : (0 ty : Dir -> Type) ->
             {n : _} ->
             (IsTupleLike Unqualified n ty, HasTableName ty) =>
             (val : ty Write) ->
             Insert ty ()
insertBase _ val = MkInsert val CNone

insertOp : Insert ty ret -> Operation ret
insertOp = singleOp . execInsert

data DInto : Type where
public export
into : Dummy DInto
into = MkDF

namespace InsertRecord
  export
  insert : (0 _ : Dummy DInto) ->
           (0 ty : Dir -> Type) ->
           {n : _} ->
           (IsTupleLike Unqualified n ty, HasTableName ty) =>
           (val : ty Write) ->
           Operation ()
  insert _ ty val = insertOp $ insertBase ty val

  export
  insert' : (0 _ : Dummy DInto) ->
            (0 ty : Dir -> Type) ->
            {n : _} ->
            (IsTupleLike Unqualified n ty, HasTableName ty) =>
            (val : ty Write) ->
            (Insert ty () -> Insert ty ret) ->
            Operation ret
  insert' _ ty val f = insertOp $ f (insertBase ty val)

namespace InsertTuple
  export
  insert : (0 _ : Dummy DInto) ->
           (0 ty : Dir -> Type) ->
           {n : _} ->
           (IsTupleLike Unqualified n ty, HasTableName ty) =>
           (val : Tuple (signatureOf ty) Write) ->
           Operation ()
  insert _ ty = insertOp . insertBase ty . fromTuple

  export
  insert' : (0 _ : Dummy DInto) ->
            (0 ty : Dir -> Type) ->
            {n : _} ->
            (IsTupleLike Unqualified n ty, HasTableName ty) =>
            (val : Tuple (signatureOf ty) Write) ->
            (Insert ty () -> Insert ty ret) ->
            Operation ret
  insert' _ ty val f = insertOp $ f (insertBase ty (fromTuple val))
