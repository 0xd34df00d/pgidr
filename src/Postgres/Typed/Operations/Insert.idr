module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple

import Postgres.Typed.Util

%default total

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

serializeElem : (se : SignatureElem) ->
                (elt : computeType' Write se) ->
                Maybe String
serializeElem (MkSE _ ty mods) elt with (computeNullability mods Write)
  _ | Nullable = toTextual <$> elt
  _ | NonNullable = Just $ toTextual elt

mapProperty' : {xs : Vect n a} ->
               (f : (x : a) -> p x -> q x) ->
               All p xs ->
               All q xs
mapProperty' f [] = []
mapProperty' f (x :: xs) = f _ x :: mapProperty' f xs

mkInsertParams' : {n : _} ->
                  {s : Signature n} ->
                  Tuple s Write ->
                  Vect n (Maybe String)
mkInsertParams' = forget . mapProperty' serializeElem

mkInsertParams : {n : _} ->
                 IsRecordType n ty =>
                 (val : ty Write) ->
                 Vect n (Maybe String)
mkInsertParams = mkInsertParams' . columns . toTuple

export
insert : HasIO io =>
         Conn s ->
         {n : _} ->
         IsRecordType n ty =>
         (val : ty Write) ->
         io (Either String ())
insert conn val = execParams conn (insertQuery val) (mkInsertParams val) >>= checkStatus
