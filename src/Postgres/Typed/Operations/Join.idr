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

export
data SigTree : (n : Nat) -> Type where
  SigLeaf : Signature n ->
            SigTree n
  SigConcat : (l : SigTree n1) ->
              (r : SigTree n2) ->
              SigTree (n1 + n2)

export
data JoinCondition : (sigl : SigTree nl) -> (sigr : SigTree nr) -> Type where
  JoinOn : Expr () Bool -> JoinCondition sigl sigr

export
toSignature : SigTree n -> Signature n
toSignature (SigLeaf sig) = sig
toSignature (SigConcat l r) = toSignature l ++ toSignature r

export
data JoinTree : (sig : SigTree n) -> (dir : Dir) -> Type where
  Leaf : (IsTupleLike n ty, IsSelectSource ty) =>
         (leaf : ty dir) ->
         JoinTree (SigLeaf $ signatureOf ty) dir
  LeafAs : (IsTupleLike n ty, IsSelectSource ty) =>
           (leaf : ty dir) ->
           (alias : String) ->
           JoinTree (SigLeaf $ aliasify alias $ signatureOf ty) dir
  Join : {sigl, sigr : _} ->
         (jtl : JoinTree sigl dir) ->
         (jtype : JoinType) ->
         (jcond : JoinCondition sigl sigr) ->
         (jtr : JoinTree sigr dir) ->
         JoinTree (SigConcat sigl sigr) dir

public export
{st : SigTree n} -> HasSignature n (JoinTree st) where
  signature = toSignature st

export
{st : SigTree n} -> IsTupleLike n (JoinTree st) where
  toTuple (Leaf leaf) = toTuple leaf
  toTuple (LeafAs leaf alias) = rewrapAliasify $ toTuple leaf
  toTuple (Join jtl jty jcond jtr) = toTuple jtl ++ toTuple jtr

  fromTuple tup = ?w2

  fromToId = ?w3
  toFromId = ?w4

public export
IsSelectSource (JoinTree n st) where
  selectSource = ?selectSource_rhs
