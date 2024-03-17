module Postgres.Typed.Tuple

import Data.List
import Data.String
import public Data.Vect.Quantifiers

import public Control.Syntax
import Data.Vect.Quantifiers.Extra

import Postgres.Typed.Modifiers
import public Postgres.Typed.PgType
import public Postgres.Typed.Signature

%default total

public export
data OpCtx = Read | Write

public export
data EffectiveNullability = Nullable | NonNullable

public export
computeNullability : List (Modifier ty) -> OpCtx -> EffectiveNullability
computeNullability mods Read =
  contains mods
    [ isNotNull ~> NonNullable
    , isSerial ~> NonNullable
    ] (otherwise Nullable)
computeNullability mods Write =
  contains mods
    [ isSerial ~> Nullable
    , isDefaulted ~> Nullable
    , isNotNull ~> NonNullable
    ] (otherwise Nullable)

public export 0
computeType : OpCtx -> (ty : Type) -> List (Modifier ty) -> Type
computeType ctx ty mods = case computeNullability mods ctx of
                               Nullable => Maybe ty
                               NonNullable => ty

public export 0
computeType' : OpCtx -> (_ : SignatureElem qk) -> Type
computeType' ctx (MkSE _ ty modifiers) = computeType ctx ty modifiers

public export
onSigVal : {ctx : OpCtx} ->
           (fNull : forall ty. PgType ty => Maybe ty -> a) ->
           (fNonNull : forall ty. PgType ty => ty -> a) ->
           (se : SignatureElem qk) ->
           (elt : computeType' ctx se) ->
           a
onSigVal fNull fNonNull (MkSE _ ty mods) elt with (computeNullability mods ctx)
  _ | Nullable = fNull elt
  _ | NonNullable = fNonNull elt

public export
onSigValUniform : {ctx : OpCtx} ->
                  (f : forall ty. PgType ty => ty -> a) ->
                  (se : SignatureElem qk) ->
                  (elt : computeType' ctx se) ->
                  Maybe a
onSigValUniform f = onSigVal (map f) (Just . f)

public export
0
Tuple : Signature qk n -> (ctx : OpCtx) -> Type
Tuple sig ctx = All (computeType' ctx) sig

export
prettyTuple : {ctx : _} -> {s : Signature qk _} -> Tuple s ctx -> String
prettyTuple tup = "{ " ++ joinBy ", " (toList $ forget $ mapPropertyRelevant showElem tup) ++ " }"
  where
  showElem : (se : SignatureElem qk) -> computeType' ctx se -> String
  showElem se elt = let value = maybe "IS NULL" ("= " ++) $ onSigValUniform show se elt
                     in "\{showName se.name} \{value}"

public export
0
tableTuple : Table n -> OpCtx -> Type
tableTuple t = Tuple t.signature

public export
0
subTuple : (0 tbl : Table n) ->
           (idxes : Vect k (Fin n)) ->
           OpCtx ->
           Type
subTuple tbl idxes = Tuple (tbl.signature `subSignature` idxes)

public export
aliasifySig : String -> SignatureElem Unqualified -> SignatureElem Qualified
aliasifySig alias (MkSE n type mods) = MkSE (QName alias n.uname) type mods  -- TODO record update syntax when Idris2#3083 is fixed

public export
aliasify : String -> Signature Unqualified n -> Signature Qualified n
aliasify alias = map (aliasifySig alias)

public export
wrapAliasify : All (computeType' ctx) sig ->
               All (computeType' ctx) (aliasify alias sig)
wrapAliasify [] = []
wrapAliasify {sig = (MkSE _ _ _ {pgType}) :: _} (x :: xs) = x :: wrapAliasify xs

public export
unwrapAliasify : {sig : _} ->
                 All (computeType' ctx) (aliasify alias sig) ->
                 All (computeType' ctx) sig
unwrapAliasify {sig = []} [] = []
unwrapAliasify {sig = (MkSE {}) :: _} (x :: xs) = x :: unwrapAliasify xs

export
unwrapWrapId : {sig : _} ->
               (alias : _) ->
               (alls : All (computeType' ctx) sig) ->
               unwrapAliasify {ctx} {alias} (wrapAliasify {ctx} {alias} alls) = alls
unwrapWrapId _ [] = Refl
unwrapWrapId {sig = (MkSE {}) :: _} alias (a :: as) = cong (a ::) (unwrapWrapId alias as)

export
wrapUnwrapId : {sig : _} ->
               (alias : _) ->
               (alls : All (computeType' ctx) (aliasify alias sig)) ->
               wrapAliasify {sig} {ctx} {alias} (unwrapAliasify {ctx} {alias} alls) = alls
wrapUnwrapId {sig = []} _ [] = Refl
wrapUnwrapId {sig = (MkSE {}) :: _} alias (a :: as) = cong (a ::) (wrapUnwrapId alias as)
