module Postgres.Typed.Modifiers

import Data.String

import Postgres.Typed.PgType
import Postgres.Typed.Signature
import Postgres.Typed.Tuple

%default total
%prefix_record_projections off

public export
data Modifiers : (ty : Type) -> Type where
  PKey   : Modifiers ty
  References : (0 other : Type) ->
               IsTableType n other =>
               (idx : Fin n) ->
               {auto isNotNull : (idx `index` signatureOf other).isNull = NonNullable} ->
               {auto typesMatch : ty = (idx `index` signatureOf other).type} ->
               Modifiers ty

public export
Show ty => Show (Modifiers ty) where
  show PKey = "PRIMARY KEY"
  show (References other idx) = "REFERENCES(" ++ tableNameOf other ++ "." ++ (idx `index` signatureOf other).name ++ ")"

public export
record ThatIs (0 ty : Type) (modifiers : List (Modifiers ty)) where
  constructor MkThatIs
  val : ty

public export
{modifiers : _} -> Show ty => Show (ThatIs ty modifiers) where
  show wm = show wm.val ++ " " ++ unwords (show <$> modifiers)

public export
{modifiers : _} -> PgType ty => PgType (ThatIs ty modifiers) where
  toTextual = toTextual . .val
  fromTextual = map MkThatIs . fromTextual
