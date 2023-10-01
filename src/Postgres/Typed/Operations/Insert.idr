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

computeName : (se : SignatureElem) -> computeType' Write se -> Maybe String
computeName (MkSE _ ty mods) elt with (computeNullability mods Write)
  _ | r = ?rhs

mkQueryFields : {n : _} ->
                IsRecordType n ty =>
                (val : ty Write) ->
                (k ** Vect k String)
mkQueryFields = catMaybes
              . forget
              . mapProperty' (\se => onSigValUniform (const se.name) se)
              . columns
              . toTuple

export
insertQuery : {n : _} ->
              IsRecordType n ty =>
              (val : ty Write) ->
              String
insertQuery val =
  let (k ** names) = mkQueryFields val
      namesStr = joinBy ", " $ toList names
      placeholders = joinBy ", "
                   $ toList
                   $ tabulate {len = k} (\i => "$" ++ show (finToNat i + 1))
   in "INSERT INTO \{tableNameOf ty} (\{namesStr}) VALUES (\{placeholders})"

mkInsertParams : {n : _} ->
                 IsRecordType n ty =>
                 (val : ty Write) ->
                 (k ** Vect k (Maybe String))
mkInsertParams = filter isJust
               . forget
               . mapProperty' (onSigValUniform toTextual)
               . columns
               . toTuple

public export
record Insert (ty : Dir -> Type) where
  constructor MkInsert
  {fieldsCount : Nat}
  {auto tyIsRecord : IsRecordType fieldsCount ty}
  valueToInsert : ty Write

data DInto : Type where
public export
into : Dummy DInto
into = MkDF

export
insert : Dummy DInto ->
         (ty : Dir -> Type) ->
         {n : _} ->
         IsRecordType n ty =>
         (val : ty Write) ->
         Insert ty
insert _ _ val = MkInsert val

export
Operation (Insert ty) where
  returnType _ = ()
  execute conn (MkInsert val) =
    execParams conn (insertQuery val) (snd $ mkInsertParams val) >>= checkStatus
