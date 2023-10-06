module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class

%default total
%prefix_record_projections off

mapProperty' : {xs : Vect n a} ->
               (f : (x : a) -> p x -> q x) ->
               All p xs ->
               All q xs
mapProperty' f [] = []
mapProperty' f (x :: xs) = f _ x :: mapProperty' f xs

record InsertColumn where
  constructor MkIC
  colName : String
  value : String

mkInsertQuery : {k : _} ->
                {0 ty : _} ->
                HasSignature n ty =>
                (cols : Vect k InsertColumn) ->
                String
mkInsertQuery cols =
  let namesStr = joinBy ", " $ toList $ .colName <$> cols
      placeholders = joinBy ", "
                   $ toList
                   $ tabulate {len = k} (\i => "$" ++ show (finToNat i + 1))
   in "INSERT INTO \{tableNameOf ty} (\{namesStr}) VALUES (\{placeholders})"

mkInsertColumns : IsRecordType n ty =>
                  (val : ty Write) ->
                  (k ** Vect k InsertColumn)
mkInsertColumns = catMaybes
                . forget
                . mapProperty' (\se => onSigValUniform (MkIC se.name . toTextual) se)
                . columns
                . toTuple

public export
record Insert (ty : Dir -> Type) where
  constructor MkInsert
  tyIsRecord : IsRecordType fieldsCount ty    -- TODO make auto implicit when Idris2#3083 is fixed
  value : ty Write

data DInto : Type where
public export
into : Dummy DInto
into = MkDF

namespace InsertRecord
  export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           IsRecordType n ty =>
           (val : ty Write) ->
           Insert ty
  insert _ _ val = MkInsert %search val

namespace InsertTuple
  export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           IsRecordType n ty =>
           (val : Tuple (signatureOf ty) Write) ->
           Insert ty
  insert d ty = insert d ty . fromRawTuple

export
Operation (Insert ty) where
  returnType _ = ()
  execute conn (MkInsert _ val) =
    let (_ ** cols) = mkInsertColumns val
        query = mkInsertQuery {ty} cols
        params = map (Just . .value) cols
     in execParams conn query params >>= checkStatus
