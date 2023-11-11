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
  SigConcat : {nl, nr : Nat} ->
              (sigl : SigTree nl) ->
              (jtype : JoinType) ->
              (sigr : SigTree nr) ->
              (jcond : JoinCondition sigl sigr) ->
              SigTree (nl + nr)

public export
toSig : SigTree n -> Signature n
toSig (SigLeaf ty) = signatureOf ty
toSig (SigLeafAs ty alias) = aliasify alias $ signatureOf ty
toSig (SigConcat l _ r _) = toSig l ++ toSig r

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
interface HasSigTree n (0 ty : Dir -> Type) | ty where
  sigTree : SigTree n

public export
{st : SigTree n} -> HasSigTree n (JoinTree st) where
  sigTree = st

public export
sigTreeOf : (0 ty : _) -> HasSigTree n ty => SigTree n
sigTreeOf ty = sigTree {ty}

public export
{st : SigTree n} -> HasSignature n (JoinTree st) where
  signature = toSig st

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

public export
table : (ty : Dir -> Type) ->
        IsTupleLike n ty =>
        IsSelectSource ty =>
        Dir -> Type
table ty = JoinTree (SigLeaf ty)

public export
crossJoin : {n1, n2 : _} ->
            (jt1, jt2 : Dir -> Type) ->
            HasSigTree n1 jt1 =>
            HasSigTree n2 jt2 =>
            Dir -> Type
crossJoin jt1 jt2 = JoinTree $ SigConcat
                                  (sigTreeOf jt1)
                                  Inner
                                  (sigTreeOf jt2)
                                  (JoinOn $ EConst $ PCBool True)
