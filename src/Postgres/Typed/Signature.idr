module Postgres.Typed.Signature

import Data.List.Quantifiers
import Decidable.Equality

import Postgres.Typed.PgType

%default total

public export
data SignatureElem : Type where
  MkSE : (name : String) ->
         (ty : Type) ->
         {auto pgType : PgType ty} ->
         SignatureElem

public export
Signature : Type
Signature = List SignatureElem

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

-- TODO terribly inefficient to do at runtime since it's quadratic,
-- but works for a PoC
data SigSub : (sig, sig' : Signature) -> Type where
  MkSS : All (`ElemSubList` sig') sig ->
         sig `SigSub` sig'

pgTySub : (ty, ty' : Type) -> (PgType ty, PgType ty') => Dec (ty `PgTySub` ty')
pgTySub ty ty' = ?pgTySub_rhs_1

elemSub : (e, e' : SignatureElem) -> Dec (e `ElemSub` e')
elemSub (MkSE name ty) (MkSE name' ty') =
  case name `decEq` name' of
       Yes Refl => case ty `pgTySub` ty' of
                        Yes prf => Yes $ MkES prf
                        No contra => No $ \(MkES prf) => contra prf
       No contra => No $ \(MkES _) => contra Refl

Uninhabited (ElemSubList e []) where
  uninhabited (ESLHere x) impossible
  uninhabited (ESLThere x) impossible

elemSubList : (e : SignatureElem) -> (sig : Signature) -> Dec (e `ElemSubList` sig)
elemSubList _ [] = No uninhabited
elemSubList e (e' :: rest) = ?elemSubList_rhs_1

sigSub : (sig, sig' : Signature) -> Dec (sig `SigSub` sig')
sigSub [] sig' = Yes (MkSS [])
sigSub (e :: sig) sig' = ?sigSub_rhs_1
