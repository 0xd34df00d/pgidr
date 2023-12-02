module Data.Vect.Quantifiers.Extra

import Data.Vect
import Data.Vect.Quantifiers

%default total

export
mapProperty' : {xs : Vect n a} ->
               (f : (x : a) -> p x -> q x) ->
               All p xs ->
               All q xs
mapProperty' f [] = []
mapProperty' f (x :: xs) = f _ x :: mapProperty' f xs

export
concatSplitInverse : {n : Nat} ->
                     (xs : Vect n a) ->
                     (ys : Vect m a) ->
                     splitAt n (xs ++ ys) = (xs, ys)
concatSplitInverse [] ys = Refl
concatSplitInverse {n = S n} (x :: xs) ys with (splitAt n (xs ++ ys)) proof p
 _ | (xs', ys') = case biinjective (sym p `trans` concatSplitInverse xs ys) of (Refl, Refl) => Refl

public export
splitAt : (n : Nat) ->
          {xs : Vect (n + m) a} ->
          (as : All p xs) ->
          (All p (fst $ splitAt {m} n xs), All p (snd $ splitAt {m} n xs))
splitAt 0 as = ([], as)
splitAt (S n) {xs = _ :: xs} (a :: as) with (splitAt n as) | (splitAt n xs)
  _ | (asn, asm) | (xsn, xsm) = (a :: asn, asm)
