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
           {auto ∊u : ty `∊` u} ->
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

  namespace NullSub
    infix 6 <:

    public export
    data (<:) : (n, n' : Nullability) -> Type where
      NSRefl : n <: n
      NSMaybe : NonNullable <: Nullable

    export
    nullSub : (n, n' : _) -> Dec (n <: n')
    nullSub Nullable Nullable = Yes NSRefl
    nullSub Nullable NonNullable = No $ \case NSRefl impossible
                                              NSMaybe impossible
    nullSub NonNullable Nullable = Yes NSMaybe
    nullSub NonNullable NonNullable = Yes NSRefl

  namespace ElemSub
    infix 6 <:

    public export
    data (<:) : (e, e' : SignatureElem) -> Type where
      MkES : n <: n' ->
             {auto ∊u : ty `∊` u} ->
             MkSE name ty n <: MkSE name ty n'

    elemSubSameNames : ty1 `∊` u =>
                       ty2 `∊` u =>
                       MkSE n1 ty1 _ <: MkSE n2 ty2 _ ->
                       n1 = n2
    elemSubSameNames (MkES _) = Refl

    elemSubSameTypes : {auto in1 : ty1 `∊` u} ->
                       {auto in2 : ty2 `∊` u} ->
                       MkSE _ ty1 null1 <: MkSE _ ty2 null2 ->
                       in1 = in2
    elemSubSameTypes (MkES _) = Refl

    elemSubNullSub : ty `∊` u ->
                     MkSE _ ty null1 <: MkSE _ ty null2 ->
                     null1 <: null2
    elemSubNullSub _ (MkES prf) = prf

    export
    elemSub : (e, e' : SignatureElem) -> Dec (e <: e')
    elemSub (MkSE name1 ty1 null1 {∊u = in1}) (MkSE name2 ty2 null2 {∊u = in2}) =
      case decEq name1 name2 of
           No contra => No $ contra . elemSubSameNames
           Yes Refl => case in1 `inDecEq` in2 of
                            No contra => No $ contra . elemSubSameTypes
                            Yes Refl => case null1 `nullSub` null2 of
                                             Yes prf => Yes (MkES prf {∊u = in2})
                                             No contra => No $ contra . elemSubNullSub in2

  public export
  data ElemSubList : (e : SignatureElem) -> (sig : Signature) -> Type where
    ESLHere   : e <: e' ->
                e `ElemSubList` e' :: rest
    ESLThere  : e `ElemSubList` rest ->
                e `ElemSubList` _  :: rest

  eslElimVoid : Not (e <: e') ->
                Not (e `ElemSubList` rest) ->
                Not (e `ElemSubList` (e' :: rest))
  eslElimVoid contra _ (ESLHere prf) = contra prf
  eslElimVoid _ contra' (ESLThere prf) = contra' prf

  export
  elemSubList : (e : SignatureElem) -> (sig : Signature) -> Dec (e `ElemSubList` sig)
  elemSubList _ [] = No $ \case ESLHere impossible
                                ESLThere impossible
  elemSubList e (e' :: rest) =
    case e `elemSub` e' of
         Yes prf => Yes (ESLHere prf)
         No contra => case e `elemSubList` rest of
                           Yes prf => Yes (ESLThere prf)
                           No contra' => No $ eslElimVoid contra contra'

  infix 6 <:
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
  public export
  data (<:) : (sig, sig' : Signature) -> Type where
    MkSS : All (`ElemSubList` sig') sig ->
           sig <: sig'

  sigSubHead : e :: sig <: sig' ->
               e `ElemSubList` sig'
  sigSubHead (MkSS (prf :: _)) = prf

  sigSubTail : e :: sig <: sig' ->
               sig <: sig'
  sigSubTail (MkSS (_ :: prfs)) = MkSS prfs

  -- TODO terribly inefficient to do at runtime since it's quadratic,
  -- but works for a PoC
  export
  sigSub : (sig, sig' : Signature) -> Dec (sig <: sig')
  sigSub [] sig' = Yes (MkSS [])
  sigSub (e :: sig) sig' =
    case e `elemSubList` sig' of
         No contra => No $ contra . sigSubHead
         Yes prf => case sig `sigSub` sig' of
                         No contra => No $ contra . sigSubTail
                         Yes (MkSS prfs) => Yes (MkSS (prf :: prfs))
