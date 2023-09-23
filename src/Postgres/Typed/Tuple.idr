module Postgres.Typed.Tuple

import Data.List

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
                                   Read => columnNull
                                   Write => case find (\e => isSerial e || isDefaulted e) mods of
                                                 Just _ => Nullable
                                                 Nothing => columnNull
  where
  columnNull : EffectiveNullability
  columnNull = case find isNotNull mods of
                    Just _ => NonNullable
                    Nothing => Nullable

public export
computeType : Dir -> (ty : Type) -> List (Modifier ty) -> Type
computeType dir ty mods = case computeNullability mods dir of
                               Nullable => Maybe ty
                               NonNullable => ty

public export
data Tuple : Signature n -> (dir : Dir) -> Type where
  Nil   : Tuple [] dir
  (::)  : {name, modifiers, sig : _} ->
          PgType ty =>
          (val : computeType dir ty modifiers) ->
          (rest : Tuple sig dir) ->
          Tuple (MkSE name ty modifiers :: sig) dir

export
{dir : _} -> Show (Tuple sig dir) where
  show tup = "(" ++ go "" tup ++ ")"
    where
    go : {dir' : _} -> String -> Tuple sig' dir' -> String
    go _ [] = ""
    go pref ((::) {name} {modifiers} val rest) with (computeNullability modifiers dir')
      _ | Nullable = case val of
                          Nothing => pref ++ name ++ " is null" ++ go ", " rest
                          Just val => pref ++ name ++ " = " ++ show val ++ go ", " rest
      _ | NonNullable = pref ++ name ++ " = " ++ show val ++ go ", " rest

public export
record NamedTuple (name : String) (s : Signature n) (dir : Dir) where
  constructor MkNT
  columns : Tuple s dir


public export
{name : _} -> {s : Signature n} -> HasSignature n (NamedTuple name s dir) where
  tableName = name
  signature = s

{- TODO, if the IsTableType type is needed at all
public export
interface HasSignature n ty => IsTableType n (0 ty : Type) | ty where
  toTuple : ty -> Tuple dir (signatureOf ty)
  fromTuple : Tuple dir (signatureOf ty) -> ty

  fromToId : (v : ty) ->
             fromTuple (toTuple v) = v
  toFromId : (v : Tuple (signatureOf ty)) ->
             toTuple (fromTuple v) = v

public export
{name : _} -> {s : Signature n} -> IsTableType n (NamedTuple name s) where
  toTuple = columns
  fromTuple = MkNT

  fromToId (MkNT columns) = Refl
  toFromId v = Refl
  -}
