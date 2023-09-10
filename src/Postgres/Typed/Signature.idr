module Postgres.Typed.Signature

import public Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality

import Postgres.Typed.PgType

%default total

public export
TypeLookup : Type
TypeLookup = Int -> SomePgType

export
defLookup : TypeLookup
defLookup 23 = MkSomePgType Integer
defLookup 25 = MkSomePgType String
defLookup _ = MkSomePgType UnknownPgType


public export
data Nullability = Nullable | NonNullable

public export
applyIsNull : Nullability -> Type -> Type
applyIsNull Nullable ty = Maybe ty
applyIsNull NonNullable ty = ty

public export
data SignatureElem : Type where
  MkSE : (name : String) ->
         (ty : Type) ->
         (isNull : Nullability) ->
         PgType ty =>
         SignatureElem

infixl 7 @:, @:?
public export
(@:), (@:?) : (name : String) ->
              (ty : Type) ->
              PgType ty =>
              SignatureElem
name @: ty = MkSE name ty NonNullable
name @:? ty = MkSE name ty Nullable

public export
Signature : Nat -> Type
Signature n = Vect n SignatureElem
