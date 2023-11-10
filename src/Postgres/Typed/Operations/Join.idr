module Postgres.Typed.Operations.Join

import Data.Vect.Quantifiers.Extra

import Postgres.Typed.Signature
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.Select

%default total
%prefix_record_projections off

record CrossJoin (lty, rty : Dir -> Type) (dir : Dir) where
  constructor MkCJR
  left : lty dir
  right : rty dir

[CJHS]
  (HasSignature n1 ty1, HasSignature n2 ty2) =>
  HasSignature (n1 + n2) (CrossJoin ty1 ty2)
  where
  signature = signatureOf ty1 ++ signatureOf ty2

%hint %inline
ITLimpliesHS : IsTupleLike n1 ty1 =>
               IsTupleLike n2 ty2 =>
               HasSignature (n1 + n2) (CrossJoin ty1 ty2)
ITLimpliesHS = CJHS

0
hsConsistent : IsTupleLike n1 ty1 =>
               IsTupleLike n2 ty2 =>
               (hasSig : HasSignature (n1 + n2) (CrossJoin ty1 ty2)) ->
               signatureOf _ {hasSig} = signatureOf (CrossJoin ty1 ty2) {hasSig = ITLimpliesHS}
hsConsistent = believe_me ()

toTupleCJ : IsTupleLike n1 ty1 =>
            IsTupleLike n2 ty2 =>
            (cj : CrossJoin ty1 ty2 dir) ->
            Tuple (signatureOf (CrossJoin ty1 ty2) {hasSig = ITLimpliesHS}) dir
toTupleCJ (MkCJR left right) = toTuple left ++ toTuple right

fromTupleCJ : {n1, n2 : Nat} ->
              IsTupleLike n1 ty1 =>
              IsTupleLike n2 ty2 =>
              Tuple (signatureOf (CrossJoin ty1 ty2) {hasSig = ITLimpliesHS}) dir ->
              CrossJoin ty1 ty2 dir
fromTupleCJ tup with (splitAt n1 tup)
  _ | (xs, ys) = let prf = sym $ concatSplitInverse (signatureOf ty1) (signatureOf ty2)
                  in MkCJR
                      (fromTuple $ rewrite cong fst prf in xs)
                      (fromTuple $ rewrite cong snd prf in ys)

%hint
CJITL : {n1, n2 : Nat} ->
        IsTupleLike n1 ty1 =>
        IsTupleLike n2 ty2 =>
        IsTupleLike (n1 + n2) (CrossJoin ty1 ty2)
CJITL = let sig : (HasSignature (n1 + n2) (CrossJoin ty1 ty2)) = ITLimpliesHS
         in MkIsTupleLike
              (\cj => rewrite hsConsistent sig in toTupleCJ cj)
              (\tup => fromTupleCJ (rewrite sym $ hsConsistent sig in tup))
              ?cj'fromto
              ?cj'tofrom

IsSelectSource lty => IsSelectSource rty => IsSelectSource (CrossJoin lty rty) where
  selectSource = selectSourceOf lty ++ ", " ++ selectSourceOf rty

{-

public export
data JoinType = Inner | Left | Right | Full

public export
data JoinCond : (lty, rty : Dir -> Type) where

public export
record JoinRec (lty, rty : Dir -> Type) (type : JoinType) (cond : JoinCond lty rty) where
  constructor MkJoinRec
  type : JoinType

public export
Join : (lty, rty : a) -> JoinType -> JoinCond -> Dir -> Type
Join _ _ _ _ Write = YouCannotWriteIntoJoinsSilly
Join lty rty type cond Read = JoinRec lty rty type cond

HasSignature n (Join lty rty type cond) where
  tableName = ?rhs
  signature = sig
  -}
