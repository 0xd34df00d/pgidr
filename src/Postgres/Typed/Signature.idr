module Postgres.Typed.Signature

import Data.List.Quantifiers

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
  Refl      : ty `PgTySub` ty'
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
