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
DefU = [uni Int, uni Integer, uni String, uni UnknownPgType]

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
           ty `∊` u =>
           SignatureElem

  infixl 7 @:

  public export
  (@:) : (name : String) ->
         (ty : Type) ->
         noMaybe ty `∊` u =>
         SignatureElem
  name @: ty = MkSE name (noMaybe ty) $ case ty of
                                             Maybe ty => Nullable
                                             ty => NonNullable

  public export
  Signature : Type
  Signature = List SignatureElem

  public export
  data NullSub : (n, n' : Nullability) -> Type where
    NSRefl : n `NullSub` n
    NSMaybe : Nullable `NullSub` NonNullable

  export
  nullSub : (n, n' : _) -> Dec (n `NullSub` n')
  nullSub Nullable Nullable = Yes NSRefl
  nullSub Nullable NonNullable = Yes NSMaybe
  nullSub NonNullable Nullable = No $ \case NSRefl impossible
                                            NSMaybe impossible
  nullSub NonNullable NonNullable = Yes NSRefl

  public export
  data ElemSub : (e, e' : SignatureElem) -> Type where
    MkES : n `NullSub` n' ->
           ty `∊` u =>
           MkSE name ty n `ElemSub` MkSE name ty n'

  elemSubSameNames : ty1 `∊` u =>
                     ty2 `∊` u =>
                     MkSE n1 ty1 null1 `ElemSub` MkSE n2 ty2 null2 ->
                     n1 = n2
  elemSubSameNames (MkES _) = Refl

  export
  elemSub : (e, e' : _) -> Dec (e `ElemSub` e')
  elemSub (MkSE name1 ty1 null1) (MkSE name2 ty2 null2) =
    case decEq name1 name2 of
         No contra => No $ contra . elemSubSameNames
         Yes Refl =>
          case _ of
               case_val => ?w1

{-
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
