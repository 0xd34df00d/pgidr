module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class

%default total
%prefix_record_projections off

mkValuesPlaceholders : (n : Nat) ->
                       String
mkValuesPlaceholders n = joinBy ", "
                       $ toList
                       $ tabulate {len = n} (\n => "$" ++ show (finToNat n + 1))

export
insertQuery : {n : _} ->
              HasSignature n ty =>
              (val : ty Write) ->
              String
insertQuery val = "INSERT INTO \{tableNameOf ty} VALUES (\{mkValuesPlaceholders n})"

mapProperty' : {xs : Vect n a} ->
               (f : (x : a) -> p x -> q x) ->
               All p xs ->
               All q xs
mapProperty' f [] = []
mapProperty' f (x :: xs) = f _ x :: mapProperty' f xs

mkInsertParams : {n : _} ->
                 IsRecordType n ty =>
                 (val : ty Write) ->
                 (k ** Vect k (Maybe String))
mkInsertParams = filter isJust
               . forget
               . mapProperty' (onSigVal (toTextual <$>) (Just . toTextual))
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
    execParams conn (insertQuery val) (mkInsertParams val) >>= checkStatus
