module Postgres.Typed.Operations.Join

import Data.Vect.Quantifiers.Extra

import Postgres.Typed.Signature
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.Select

%default total
%prefix_record_projections off

public export
data JoinType = Inner | Left | Right | Full

public export
data JoinCondition : (sigl : Signature nl) -> (sigr : Signature nr) -> Type where
  JoinOn : Expr () Bool -> JoinCondition sigl sigr
  {- TODO
  JoinUsing : (name : String) ->
              All (\name => Either (name `InSignature` sigl) (name `InSignature` sigr)) names ->
              JoinCondition sigl sigr
              -}

export
data JoinTree : (n : Nat) -> (sig : Signature n) -> (dir : Dir) -> Type where
  Leaf : (IsTupleLike n ty, IsSelectSource ty) =>
         (leaf : ty dir) ->
         JoinTree n (signatureOf ty) dir
  Join : {sigl, sigr : _} ->
         (jtl : JoinTree nl sigl dir) ->
         (jtype : JoinType) ->
         (jcond : JoinCondition sigl sigr) ->
         (jtr : JoinTree nr sigr dir) ->
         JoinTree (nl + nr) (sigl ++ sigr) dir

public export
{sig : Signature n} -> HasSignature n (JoinTree n sig) where
  signature = sig

export
{sig : Signature n} -> IsTupleLike n (JoinTree n sig) where
  toTuple (Leaf leaf) = toTuple leaf
  toTuple (Join jtl jty jcond jtr) = toTuple jtl ++ toTuple jtr

  fromTuple tup = ?w2

  fromToId = ?w3
  toFromId = ?w4

public export
IsSelectSource (JoinTree n sig) where
  selectSource = ?selectSource_rhs
