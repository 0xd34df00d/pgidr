module Postgres.Typed.Modifiers

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
record ThatIs (0 ty : Type) (modifiers : List (Modifier ty)) where
  constructor MkThatIs
  val : ty

public export
{modifiers : _} -> Show ty => Show (ty `ThatIs` modifiers) where
  show wm = show wm.val ++ " " ++ unwords (show <$> modifiers)

public export
{modifiers : _} -> Num ty => Num (ty `ThatIs` modifiers) where
  fromInteger = MkThatIs . fromInteger
  v1 * v2 = MkThatIs $ v1.val * v2.val
  v1 + v2 = MkThatIs $ v1.val + v2.val

public export
{modifiers : _} -> PgType ty => PgType (ty `ThatIs` modifiers) where
  toTextual = toTextual . .val
  fromTextual = map (\v => MkThatIs v) . fromTextual

public export
{modifiers : _} -> CreatablePgType ty => CreatablePgType (ty `ThatIs` modifiers) where
  fieldTypeName = fieldTypeNameOf ty ++ " " ++ unwords (show <$> modifiers)
