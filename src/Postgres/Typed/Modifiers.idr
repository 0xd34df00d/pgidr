module Postgres.Typed.Modifiers

import Data.List.Elem
import Data.Vect.Quantifiers
import Data.String

import Postgres.Typed.PgType
import Postgres.Typed.Signature
import Postgres.Typed.Tuple

%default total
%prefix_record_projections off

public export
data Modifier : (ty : Type) -> Type where
  PKey   : Modifier ty
  Serial : Modifier Integer
  References : (0 other : Type) ->
               IsTableType n other =>
               (idx : Fin n) ->
               {auto isNotNull : (idx `index` signatureOf other).isNull = NonNullable} ->
               {auto typesMatch : ty = (idx `index` signatureOf other).type} ->
               Modifier ty
  Default : (defVal : ty) ->
            Modifier ty

public export
Show ty => Show (Modifier ty) where
  show PKey = "PRIMARY KEY"
  show Serial = "SERIAL"
  show (References other idx) = "REFERENCES(" ++
                                tableNameOf other ++ "." ++ (idx `index` signatureOf other).name ++
                                ")"
  show (Default defVal) = "DEFAULT " ++ show defVal

public export
data MVSerialNoPKey : (mods : List (Modifier ty)) -> Type where
  MVSNP'NoSerial : (Not (Serial `Elem` mods)) -> MVSerialNoPKey mods
  MVSNP'Serial : (Serial `Elem` mods) ->
                 (Not (PKey `Elem` mods)) ->
                 MVSerialNoPKey mods

public export
0 ModifiersValid : (mods : List (Modifier ty)) -> Type
ModifiersValid mods = All id [MVSerialNoPKey mods, NonEmpty mods]

public export
record ThatIs (0 ty : Type) (modifiers : List (Modifier ty)) where
  constructor MkThatIs
  val : ty
  {auto 0 modifiersValid : ModifiersValid modifiers}

public export
{modifiers : _} -> Show ty => Show (ty `ThatIs` modifiers) where
  show wm = show wm.val ++ " " ++ unwords (show <$> modifiers)

public export
{modifiers : _} -> ModifiersValid modifiers => PgType ty => PgType (ty `ThatIs` modifiers) where
  toTextual = toTextual . .val
  fromTextual = map (\v => MkThatIs v) . fromTextual
