module Postgres.Typed.Operations.Join

import Data.Vect.Quantifiers.Extra

import Postgres.Typed.Signature
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.Select

%default total
%prefix_record_projections off

public export
aliasifySig : String -> SignatureElem -> SignatureElem
aliasifySig alias (MkSE name type mods) = MkSE (alias ++ "." ++ name) type mods  -- TODO record update syntax when Idris2#3083 is fixed

public export
aliasify : String -> Signature n -> Signature n
aliasify alias = map (aliasifySig alias)

rewrapAliasify : All (computeType' dir) sig ->
                 All (computeType' dir) (aliasify alias sig)
rewrapAliasify [] = []
rewrapAliasify {sig = (MkSE _ _ _ {pgType}) :: _} (x :: xs) = x :: rewrapAliasify xs


public export
data JoinType = Inner | Left | Right | Full

public export
data SigTree : (n : Nat) -> Type

public export
data JoinCondition : (sigl : SigTree nl) -> (sigr : SigTree nr) -> Type where
  JoinOn : Expr () Bool -> JoinCondition sigl sigr

public export
data SigTree : (n : Nat) -> Type where
  SigLeaf : (0 ty : _) ->
            (IsTupleLike n ty, IsSelectSource ty) =>
            SigTree n
  SigLeafAs : (ty : _) ->
              (IsTupleLike n ty, IsSelectSource ty) =>
              (alias : String) ->
              SigTree n
  SigConcat : (sigl : SigTree nl) ->
              (jtype : JoinType) ->
              (sigr : SigTree nr) ->
              (jcond : JoinCondition sigl sigr) ->
              SigTree (nl + nr)

public export
toSignature : SigTree n -> Signature n
toSignature (SigLeaf ty) = signatureOf ty
toSignature (SigLeafAs ty alias) = aliasify alias $ signatureOf ty
toSignature (SigConcat l _ r _) = toSignature l ++ toSignature r

public export
data JoinTree : (st : SigTree n) -> (dir : Dir) -> Type where
  Leaf : (IsTupleLike n ty, IsSelectSource ty) =>
         (leaf : ty dir) ->
         JoinTree (SigLeaf ty) dir
  LeafAs : (IsTupleLike n ty, IsSelectSource ty) =>
           (leaf : ty dir) ->
           (alias : String) ->
           JoinTree (SigLeafAs ty alias) dir
  Join : {sigl : SigTree nl} ->
         {sigr : SigTree nr} ->
         {jcond : JoinCondition sigl sigr} ->
         (jtl : JoinTree sigl dir) ->
         (jtr : JoinTree sigr dir) ->
         JoinTree (SigConcat sigl jtype sigr jcond) dir

public export
{st : SigTree n} -> HasSignature n (JoinTree st) where
  signature = toSignature st

export
{st : SigTree n} -> IsTupleLike n (JoinTree st) where
  toTuple (Leaf leaf) = toTuple leaf
  toTuple (LeafAs leaf alias) = rewrapAliasify $ toTuple leaf
  toTuple (Join jtl jtr) = toTuple jtl ++ toTuple jtr

  fromTuple tup = ?w2

  fromToId = ?w3
  toFromId = ?w4

public export
IsSelectSource (JoinTree st) where
  selectSource = ?selectSource_rhs
