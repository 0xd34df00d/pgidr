module Postgres.Typed.Operations.Join

import Data.Vect.Quantifiers.Extra
import Derive.Prelude

import Postgres.Typed.Signature
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.Select

%language ElabReflection
%default total
%prefix_record_projections off

public export
data JoinType = Inner | Left | Right | Full
%runElab derive "JoinType" [Eq, Ord, Show]

public export
data SigTree : (n : Nat) -> Type

public export
data JoinCondition : (sigl : SigTree nl) -> (sigr : SigTree nr) -> Type where
  JoinOn : Expr () Bool -> JoinCondition sigl sigr

namespace JCOverloads
  export
  toFromPart : JoinCondition sigl sigr -> String
  toFromPart (JoinOn expr) = "ON " ++ toQueryPart expr

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

public export
{st : SigTree n} -> IsTupleLike n (JoinTree st) where
  toTuple (Leaf leaf) = toTuple leaf
  toTuple (LeafAs leaf) = wrapAliasify $ toTuple leaf
  toTuple (Join jtl jtr) = toTuple jtl ++ toTuple jtr

  fromTuple tup with (st)
   _ | SigLeaf ty = Leaf $ fromTuple tup
   _ | SigLeafAs ty alias = LeafAs $ fromTuple $ unwrapAliasify tup
   _ | SigConcat {nl} sigl jtype sigr jcond with (splitAt nl tup)
     _ | (tupl, tupr) = let prf = sym $ concatSplitInverse (toSig sigl) (toSig sigr)
                         in Join
                             (fromTuple $ rewrite cong fst prf in tupl)
                             (fromTuple $ rewrite cong snd prf in tupr)

  fromToId = ?w3
  toFromId = ?w4

namespace SigTreeOverloads
  export
  toFromPart : SigTree n -> String
  toFromPart (SigLeaf ty) = selectSourceOf ty
  toFromPart (SigLeafAs ty alias) = "\{selectSourceOf ty} AS \{alias}"
  toFromPart (SigConcat sigl jtype sigr jcond) = "\{toFromPart sigl} \{show jtype} JOIN \{toFromPart sigr} \{toFromPart jcond}"

public export
{st : SigTree n} -> IsSelectSource (JoinTree st) where
  selectSource = toFromPart st

public export
{dir, st : _} -> Show (JoinTree st dir) where
  show jt = "\{toFromPart st} \{prettyTuple $ toTuple jt}"

public export
table : (ty : Dir -> Type) ->
        IsTupleLike n ty =>
        IsSelectSource ty =>
        Dir -> Type
table ty = JoinTree (SigLeaf ty)

infix 3 `as`
public export
as : (ty : Dir -> Type) ->
     (alias : String) ->
     IsTupleLike n ty =>
     IsSelectSource ty =>
     Dir -> Type
ty `as` alias = JoinTree (SigLeafAs ty alias)

infixl 2 `crossJoin`
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
