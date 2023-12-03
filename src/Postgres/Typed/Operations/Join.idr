module Postgres.Typed.Operations.Join

import Data.Vect.Quantifiers.Extra
import Derive.Prelude

import Postgres.Typed.Signature
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.SelectSource

%language ElabReflection
%default total
%prefix_record_projections off

export
data JoinType = Inner | Left | Right | Full
%runElab derive "JoinType" [Eq, Ord, Show]

public export
data SigTree : (n : Nat) -> Type

record JoinOnExprSig (sl : SigTree nl) (sr : SigTree nr) where

export
data JoinCondition : (sigl : SigTree nl) -> (sigr : SigTree nr) -> Type where
  JoinOn : Expr (JoinOnExprSig sigl sigr) Bool -> JoinCondition sigl sigr

namespace JCOverloads
  export
  toFromPart : JoinCondition sigl sigr -> String
  toFromPart (JoinOn expr) = "ON " ++ toQueryPart expr

public export
data SigTree : (n : Nat) -> Type where
  SigLeaf : (0 ty : _) ->
            IsTupleLike n ty =>
            IsSelectSource ty =>
            SigTree n
  SigLeafAs : (0 ty : _) ->
              IsTupleLike n ty =>
              IsSelectSource ty =>
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

export
data JoinTree : (st : SigTree n) -> (dir : Dir) -> Type where
  Leaf : IsTupleLike n ty =>
         IsSelectSource ty =>
         (leaf : ty dir) ->
         JoinTree (SigLeaf ty) dir
  LeafAs : IsTupleLike n ty =>
           IsSelectSource ty =>
           (leaf : ty dir) ->
           JoinTree (SigLeafAs ty alias) dir
  Join : {sigl : SigTree nl} ->
         {sigr : SigTree nr} ->
         {jcond : JoinCondition sigl sigr} ->
         (jtl : JoinTree sigl dir) ->
         (jtr : JoinTree sigr dir) ->
         JoinTree (SigConcat sigl jtype sigr jcond) dir

public export
{sl : SigTree nl} -> {sr : SigTree nr} -> HasSignature (nl + nr) (JoinOnExprSig sl sr) where
  signature = toSig sl ++ toSig sr

export
{st : SigTree n} -> HasSignature n (JoinTree st) where
  signature = toSig st

export
{st : SigTree n} -> IsTupleLike n (JoinTree st) where
  toTuple (Leaf leaf) = toTuple leaf
  toTuple (LeafAs leaf) = wrapAliasify $ toTuple leaf
  toTuple (Join jtl jtr) = toTuple jtl ++ toTuple jtr

  fromTuple tup with (st)
   _ | SigLeaf ty = Leaf $ fromTuple tup
   _ | SigLeafAs ty alias = LeafAs $ fromTuple $ unwrapAliasify tup
   _ | SigConcat {nl} sigl jtype sigr jcond =
        let splits = splitAt nl tup
            prf = sym $ concatSplitInverse (toSig sigl) (toSig sigr)
         in Join
              (fromTuple $ rewrite cong fst prf in fst splits)
              (fromTuple $ rewrite cong snd prf in snd splits)

  fromToId (Leaf leaf) = cong Leaf $ fromToId leaf
  fromToId (LeafAs {alias} leaf) = rewrite unwrapWrapId {dir} alias (toTuple leaf) in
                                           cong LeafAs $ fromToId leaf
  fromToId (Join jtl jtr) = ?w3_2
  toFromId tup with (st)
    _ | SigLeaf _ = toFromId tup
    _ | SigLeafAs ty alias = cong wrapAliasify (toFromId $ unwrapAliasify tup)
                     `trans` wrapUnwrapId alias tup
    _ | SigConcat {nl} sigl jtype sigr jcond = ?toFromId_rhs3

namespace SigTreeOverloads
  export
  toFromPart : SigTree n -> String
  toFromPart (SigLeaf ty) = selectSourceOf ty
  toFromPart (SigLeafAs ty alias) = "\{selectSourceOf ty} AS \{alias}"
  toFromPart (SigConcat sigl jtype sigr jcond) = "(\{toFromPart sigl} \{show jtype} JOIN \{toFromPart sigr} \{toFromPart jcond})"

public export
sigTreeSources : SigTree n -> List String
sigTreeSources (SigLeaf ty) = [selectSourceOf ty]
sigTreeSources (SigLeafAs ty alias) = [alias]
sigTreeSources (SigConcat sigl jtype sigr jcond) = sigTreeSources sigl ++ sigTreeSources sigr

-- TODO better error messages when this fails
public export
IsValidTree : (st : SigTree n) -> Type
IsValidTree st = let srcs := sigTreeSources st in nub srcs = srcs

export
{dir, st : _} -> Show (JoinTree st dir) where
  show jt = "\{toFromPart st} \{prettyTuple $ toTuple jt}"

public export
table : (ty : Dir -> Type) ->
        IsTupleLike n ty =>
        IsSelectSource ty =>
        SigTree n
table ty = SigLeaf ty

infix 3 `as`
public export
as : (ty : Dir -> Type) ->
     (alias : String) ->
     IsTupleLike n ty =>
     IsSelectSource ty =>
     SigTree n
ty `as` alias = SigLeafAs ty alias

infixl 2 `crossJoin`
public export
crossJoin : {n1, n2 : _} ->
            (st1 : SigTree n1) ->
            (st2 : SigTree n2) ->
            SigTree (n1 + n2)
crossJoin st1 st2 = SigConcat
                      st1
                      Inner
                      st2
                      (JoinOn $ EConst $ PCBool True)
