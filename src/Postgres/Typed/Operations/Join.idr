module Postgres.Typed.Operations.Join

import Data.Vect.Quantifiers.Extra
import Derive.Prelude

import Postgres.Typed.Signature
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Expression

%language ElabReflection
%default total
%prefix_record_projections off

export
data JoinType = Inner | Left | Right | Full
%runElab derive "JoinType" [Eq, Ord, Show]

public export
data SigTree : (n : Nat) -> Type

public export
toSig : SigTree n -> Signature Qualified n

export
data JoinCondition : (sigl : SigTree nl) -> (sigr : SigTree nr) -> Type where
  JoinOn : Expr (toSig sigl ++ toSig sigr) Bool -> JoinCondition sigl sigr

namespace JCOverloads
  export
  toFromPart : JoinCondition sigl sigr -> String
  toFromPart (JoinOn expr) = "ON " ++ toQueryPart expr

public export
data SigTree : (n : Nat) -> Type where
  SigLeaf : (tbl : Table n) ->
            (alias : String) ->
            SigTree n
  SigConcat : {nl, nr : Nat} ->
              (sigl : SigTree nl) ->
              (jtype : JoinType) ->
              (sigr : SigTree nr) ->
              (jcond : JoinCondition sigl sigr) ->
              SigTree (nl + nr)

toSig (SigLeaf tbl alias) = aliasify alias tbl.signature
toSig (SigConcat l _ r _) = toSig l ++ toSig r

export
data JoinTree : (st : SigTree n) -> Type where
  Leaf : (leaf : Tuple tbl.signature Read) ->
         JoinTree (SigLeaf tbl alias)
  Join : {sigl : SigTree nl} ->
         {sigr : SigTree nr} ->
         {jcond : JoinCondition sigl sigr} ->
         (jtl : JoinTree sigl) ->
         (jtr : JoinTree sigr) ->
         JoinTree (SigConcat sigl jtype sigr jcond)

asTuple : JoinTree st -> Tuple (toSig st) Read
asTuple (Leaf leaf) = wrapAliasify leaf
asTuple (Join jtl jtr) = asTuple jtl ++ asTuple jtr

namespace SigTreeOverloads
  export
  toFromPart : SigTree n -> String
  toFromPart (SigLeaf tbl alias) = "\{tbl.name} AS \{alias}"
  toFromPart (SigConcat sigl jtype sigr jcond) = "(\{toFromPart sigl} \{show jtype} JOIN \{toFromPart sigr} \{toFromPart jcond})"

public export
sigTreeSources : SigTree n -> List String
sigTreeSources (SigLeaf ty alias) = [alias]
sigTreeSources (SigConcat sigl jtype sigr jcond) = sigTreeSources sigl ++ sigTreeSources sigr

-- TODO better error messages when this fails
public export 0
CanBeJoined : (st1, st2 : SigTree _) -> Type
CanBeJoined st1 st2 = isect (sigTreeSources st1) (sigTreeSources st2) = []
  where
  isect : List String -> List String -> List String
  isect xs ys = [x | x <- xs, any (== x) ys]

export
{st : _} -> Show (JoinTree st) where
  show jt = "\{toFromPart st} \{prettyTuple $ asTuple jt}"

public export
table : (tbl : Table n) ->
        SigTree n
table tbl = SigLeaf tbl tbl.name

infix 3 `as`
public export
as : (tbl : Table n) ->
     (alias : String) ->
     SigTree n
ty `as` alias = SigLeaf ty alias

infixl 2 `crossJoin`
public export
crossJoin : {n1, n2 : _} ->
            (st1 : SigTree n1) ->
            (st2 : SigTree n2) ->
            CanBeJoined st1 st2 =>
            SigTree (n1 + n2)
crossJoin st1 st2 = SigConcat
                      st1
                      Inner
                      st2
                      (JoinOn $ EConst $ PCBool True)

public export
innerJoin : {n1, n2 : _} ->
            (st1 : SigTree n1) ->
            (st2 : SigTree n2) ->
            CanBeJoined st1 st2 =>
            (joinExpr : Expr (toSig st1 ++ toSig st2) Bool) ->
            SigTree (n1 + n2)
innerJoin st1 st2 joinExpr = SigConcat st1 Inner st2 (JoinOn joinExpr)
