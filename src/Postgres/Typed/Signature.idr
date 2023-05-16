module Postgres.Typed.Signature

import Data.List.Quantifiers
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
DefU = [uni Int, uni Integer, uni String]

infix 7 `∊`

public export
data ∊ : (ty : Type) -> (u : Universe) -> Type where
  Here  : ty `∊` ((ty ** _) :: _)
  There : ty `∊` u ->
          ty `∊` (_ :: u)

public export
data Nullability = Nullable | NonNullable

public export %inline %tcinline
noMaybe : Type -> Type
noMaybe ty = case ty of
                  Maybe ty => ty
                  ty => ty

parameters {u : Universe}
  public export
  data SignatureElem : Type where
    MkSE : (name : String) ->
           (ty : Type) ->
           Nullability ->
           PgType ty =>
           ty `∊` u =>
           SignatureElem

  infixl 7 @:

  public export
  (@:) : (name : String) ->
         (ty : Type) ->
         PgType (noMaybe ty) =>
         noMaybe ty `∊` u =>
         SignatureElem
  name @: ty = MkSE name (noMaybe ty) $ case ty of
                                             Maybe ty => Nullable
                                             ty => NonNullable

  public export
  Signature : Type
  Signature = List SignatureElem

{-
data PgTySub : (ty, ty' : Type) -> Type where
  Refl      : ty `PgTySub` ty
  Nullable  : Maybe ty `PgTySub` ty
  Trans     : ty₁ `PgTySub` ty₂ ->
              ty₂ `PgTySub` ty₃ ->
              ty₁ `PgTySub` ty₃

data ElemSub : (e, e' : SignatureElem) -> Type where
  MkES : (PgType pgty, PgType pgty') =>
         pgty `PgTySub` pgty' ->
         MkSE n pgty `ElemSub` MkSE n pgty'

data ElemSubList : (e : SignatureElem) -> (sig : Signature) -> Type where
  ESLHere   : e `ElemSub` e' ->
              e `ElemSubList` e' :: rest
  ESLThere  : e `ElemSubList` rest ->
              e `ElemSubList` _  :: rest

||| ``sig `SigSub` sig'``
||| means that a tuple with the signature `sig'`
||| can be safely read into a tuple with the signature `sig`,
||| perhaps with some loss of extra fields,
||| but without loss of data for each field.
|||
||| Roughly speaking, it means that the set of fields in `sig`
||| is a subset of the set of fields in `sig'`,
||| and for each field its type in `sig`
||| defines a superset of values of the corresponding type in `sig'`.
|||
||| As an example, we surely could read [("name", String), ("lastname", String)]
||| into a [("lastname", Maybe String)].
data SigSub : (sig, sig' : Signature) -> Type where
  MkSS : All (`ElemSubList` sig') sig ->
         sig `SigSub` sig'

elemSub : (e, e' : SignatureElem) -> Dec (e `ElemSub` e')
elemSub (MkSE name ty) (MkSE name' ty') =
  case name `decEq` name' of
       Yes Refl => ?elemSub_ty
       No contra => No $ \(MkES _) => contra Refl

Uninhabited (ElemSubList e []) where
  uninhabited (ESLHere x) impossible
  uninhabited (ESLThere x) impossible

elemSubList : (e : SignatureElem) -> (sig : Signature) -> Dec (e `ElemSubList` sig)
elemSubList _ [] = No uninhabited
elemSubList e (e' :: rest) = ?elemSubList_rhs_1

-- TODO terribly inefficient to do at runtime since it's quadratic,
-- but works for a PoC
sigSub : (sig, sig' : Signature) -> Dec (sig `SigSub` sig')
sigSub [] sig' = Yes (MkSS [])
sigSub (e :: sig) sig' = ?sigSub_rhs_1
-}
