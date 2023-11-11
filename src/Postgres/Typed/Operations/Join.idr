module Postgres.Typed.Operations.Join

import Data.Vect.Quantifiers.Extra

import Postgres.Typed.Signature
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Expression
import Postgres.Typed.Operations.Select

%default total
%prefix_record_projections off

public export
record CrossJoin {0 n1, n2 : Nat} (ty1, ty2 : Dir -> Type) (dir : Dir) where
  constructor MkCJR
  left : ty1 dir
  right : ty2 dir

public export
crossJoin : (ty1, ty2 : Dir -> Type) ->
            HasSignature n1 ty1 =>
            HasSignature n2 ty2 =>
            Dir ->
            Type
crossJoin ty1 ty2 = CrossJoin {n1} {n2} ty1 ty2

public export
HasSignature n1 ty1 => HasSignature n2 ty2 => HasSignature (n1 + n2) (CrossJoin {n1} {n2} ty1 ty2) where
  signature = signatureOf ty1 ++ signatureOf ty2

public export
{n1 : _} -> IsTupleLike n1 ty1 => IsTupleLike n2 ty2 => IsTupleLike (n1 + n2) (CrossJoin {n1} {n2} ty1 ty2) where
  toTuple (MkCJR left right) = toTuple left ++ toTuple right
  fromTuple tup with (splitAt n1 tup)
    _ | (xs, ys) = let prf = sym $ concatSplitInverse (signatureOf ty1) (signatureOf ty2)
                    in MkCJR
                        (fromTuple $ rewrite cong fst prf in xs)
                        (fromTuple $ rewrite cong snd prf in ys)

  fromToId = ?w3
  toFromId = ?w4

public export
Show (ty1 dir) => Show (ty2 dir) => Show (CrossJoin ty1 ty2 dir) where
  show (MkCJR left right) = "(\{show left}) × (\{show right})"

public export
IsSelectSource ty1 => IsSelectSource ty2 => IsSelectSource (CrossJoin ty1 ty2) where
  selectSource = selectSourceOf ty1 ++ ", " ++ selectSourceOf ty2
