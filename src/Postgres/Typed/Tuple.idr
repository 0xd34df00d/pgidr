module Postgres.Typed.Tuple

import Data.List
import Data.String
import public Data.Vect.Quantifiers

import Data.Vect.Quantifiers.Extra

import Postgres.Typed.Modifiers
import public Postgres.Typed.PgType
import public Postgres.Typed.Signature

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

export
prettyTuple : {dir : _} -> {s : Signature _} -> Tuple s dir -> String
prettyTuple tup = "{ " ++ joinBy ", " (toList $ forget $ mapProperty' showElem tup) ++ " }"
  where
  showElem : (se : SignatureElem) -> computeType' dir se -> String
  showElem se elt = let value = maybe "IS NULL" ("= " ++) $ onSigValUniform show se elt
                     in "\{se.name} \{value}"

public export
subTuple : (0 ty : _) ->
           HasSignature n ty =>
           (idxes : Vect k (Fin n)) ->
           Dir ->
           Type
subTuple ty idxes = Tuple (signatureOf ty `subSignature` idxes)

public export
record NamedTuple (name : String) (s : Signature n) (dir : Dir) where
  constructor MkTup
  columns : Tuple s dir

export
{dir : _} -> {name : _} -> {s : Signature n} -> Show (NamedTuple name s dir) where
  show tup = name ++ " " ++ prettyTuple tup.columns

public export
{s : Signature n} -> HasSignature n (NamedTuple name s) where
  signature = s

public export
{name : _} -> HasTableName (NamedTuple name s) where
  tableName = name

public export
interface HasSignature n ty => IsTupleLike n (0 ty : Dir -> Type) | ty where
  constructor MkIsTupleLike
  toTuple : ty dir -> Tuple (signatureOf ty) dir
  fromTuple : Tuple (signatureOf ty) dir -> ty dir

  fromToId : (v : ty dir) ->
             fromTuple (toTuple v) = v
  toFromId : (v : Tuple (signatureOf ty) dir) ->
             toTuple (fromTuple {dir} v) = v

public export
{name : _} -> {s : Signature n} -> IsTupleLike n (NamedTuple name s) where
  toTuple = .columns
  fromTuple = MkTup

  fromToId (MkTup columns) = Refl
  toFromId v = Refl

public export
aliasifySig : String -> SignatureElem -> SignatureElem
aliasifySig alias (MkSE name type mods) = MkSE (alias ++ "." ++ name) type mods  -- TODO record update syntax when Idris2#3083 is fixed

public export
aliasify : String -> Signature n -> Signature n
aliasify alias = map (aliasifySig alias)

public export
wrapAliasify : All (computeType' dir) sig ->
               All (computeType' dir) (aliasify alias sig)
wrapAliasify [] = []
wrapAliasify {sig = (MkSE _ _ _ {pgType}) :: _} (x :: xs) = x :: wrapAliasify xs

public export
unwrapAliasify : {sig : _} ->
                 All (computeType' dir) (aliasify alias sig) ->
                 All (computeType' dir) sig
unwrapAliasify {sig = []} [] = []
unwrapAliasify {sig = (MkSE {}) :: _} (x :: xs) = x :: unwrapAliasify xs
