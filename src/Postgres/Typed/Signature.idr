module Postgres.Typed.Signature

import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality

import Postgres.Typed.PgType

%default total

public export
Universe : Type
Universe = List (ty : Type ** PgType ty)

public export
uni : (ty : Type) -> (dict : PgType ty) => (a : Type ** PgType a)
uni ty = (ty ** dict)

public export
DefU : Universe
DefU = [uni Int, uni Integer, uni String, uni UnknownPgType]

infix 7 `∊`
public export
data ∊ : (ty : Type) -> (u : Universe) -> Type where
  Here  : ty `∊` ((ty ** _) :: _)
  There : ty `∊` u ->
          ty `∊` (_ :: u)

%hint
public export
uniTypeIsPgType : (0 ty : Type) -> {u : Universe} -> (prf : ty `∊` u) -> PgType ty
uniTypeIsPgType ty Here = %search
uniTypeIsPgType ty (There prf) = uniTypeIsPgType ty prf

public export
TypeLookup : {u : Universe} -> Type
TypeLookup = Int -> (ty ** ty `∊` u)

export
defLookup : TypeLookup {u = DefU}
defLookup 23 = (Integer ** %search)
defLookup 25 = (String ** %search)
defLookup _ = (UnknownPgType ** %search)


inDecEq : (in1 : ty1 `∊` u) ->
          (in2 : ty2 `∊` u) ->
          Dec (in1 = in2)
inDecEq Here Here = Yes Refl
inDecEq Here (There x) = No $ \case Refl impossible
inDecEq (There in1) Here = No $ \case Refl impossible
inDecEq (There in1) (There in2) = case in1 `inDecEq` in2 of
                                       Yes Refl => Yes Refl
                                       No contra => No $ \case Refl => contra Refl

public export
data Nullability = Nullable | NonNullable

public export
applyIsNull : Nullability -> Type -> Type
applyIsNull Nullable ty = Maybe ty
applyIsNull NonNullable ty = ty

parameters {u : Universe}
  public export
  data SignatureElem : Type where
    MkSE : (name : String) ->
           (ty : Type) ->
           (isNull : Nullability) ->
           {auto ∊u : ty `∊` u} ->
           SignatureElem

  infixl 7 @:, @:?
  public export
  (@:), (@:?) : (name : String) ->
                (ty : Type) ->
                ty `∊` u =>
                SignatureElem
  name @: ty = MkSE name ty NonNullable
  name @:? ty = MkSE name ty Nullable

  public export
  Signature : Nat -> Type
  Signature n = Vect n SignatureElem
