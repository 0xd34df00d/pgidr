module Postgres.Typed.Tuple

import Data.List
import Data.String
import public Data.Vect.Quantifiers

import Postgres.Typed.Modifiers
import public Postgres.Typed.PgType
import public Postgres.Typed.Signature
import Postgres.Typed.Util

%default total

public export
data Dir = Read | Write

public export
data EffectiveNullability = Nullable | NonNullable

public export
computeNullability : List (Modifier ty) -> Dir -> EffectiveNullability
computeNullability mods dir = case dir of
                                   Read => case find (\e => isNotNull e || isSerial e) mods of
                                                Just _ => NonNullable
                                                Nothing => Nullable
                                   Write => case find (\e => isSerial e || isDefaulted e) mods of
                                                 Just _ => Nullable
                                                 Nothing => case find isNotNull mods of
                                                                 Just _ => NonNullable
                                                                 Nothing => Nullable

public export
computeType : Dir -> (ty : Type) -> List (Modifier ty) -> Type
computeType dir ty mods = case computeNullability mods dir of
                               Nullable => Maybe ty
                               NonNullable => ty

public export
computeType' : Dir -> (_ : SignatureElem) -> Type
computeType' dir (MkSE _ ty modifiers) = computeType dir ty modifiers

public export
onSigVal : {dir : Dir} ->
           (fNull : forall ty. PgType ty => Maybe ty -> a) ->
           (fNonNull : forall ty. PgType ty => ty -> a) ->
           (se : SignatureElem) ->
           (elt : computeType' dir se) ->
           a
onSigVal fNull fNonNull (MkSE _ ty mods) elt with (computeNullability mods dir)
  _ | Nullable = fNull elt
  _ | NonNullable = fNonNull elt

public export
onSigValUniform : {dir : Dir} ->
                  (f : forall ty. PgType ty => ty -> a) ->
                  (se : SignatureElem) ->
                  (elt : computeType' dir se) ->
                  Maybe a
onSigValUniform f = onSigVal (map f) (Just . f)


public export
Tuple : Signature n -> (dir : Dir) -> Type
Tuple sig dir = All (computeType' dir) sig

prettyTuple : {dir : _} -> {s : Signature _} -> Tuple s dir -> String
prettyTuple tup = "{ " ++ joinBy ", " (toList $ forget $ mapProperty' showElem tup) ++ " }"
  where
  showElem : (se : SignatureElem) -> computeType' dir se -> String
  showElem se elt = let value = maybe "IS NULL" (" = " ++) $ onSigValUniform show se elt
                     in "\{se.name} \{value}"

public export
record NamedTuple (name : String) (s : Signature n) (dir : Dir) where
  constructor MkTup
  columns : Tuple s dir


public export
{name : _} -> {s : Signature n} -> HasSignature n (NamedTuple name s) where
  tableName = name
  signature = s

public export
{name : _} -> {s : Signature n} -> HasSignature n (NamedTuple name s dir) where
  tableName = name
  signature = s

public export
interface HasSignature n ty => IsRecordType n (0 ty : Dir -> Type) | ty where
  fromRawTuple : Tuple (signatureOf ty) dir -> ty dir

  toTuple : ty dir -> NamedTuple (tableNameOf ty) (signatureOf ty) dir
  fromTuple : NamedTuple (tableNameOf ty) (signatureOf ty) dir -> ty dir

  fromToId : (v : ty dir) ->
             fromTuple (toTuple v) = v
  toFromId : (v : NamedTuple (tableNameOf ty) (signatureOf ty) dir) ->
             toTuple (fromTuple v) = v

public export
{name : _} -> {s : Signature n} -> IsRecordType n (NamedTuple name s) where
  fromRawTuple = MkTup

  toTuple = id
  fromTuple = id

  fromToId v = Refl
  toFromId v = Refl
