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
tabulate : {n : _} ->
           {0 xs : Vect n _} ->
           (f : (ix : Fin n) -> p (ix `index` xs)) ->
           All p {n} xs
tabulate {xs = []} f = []
tabulate {xs = _ :: _} f = f FZ :: tabulate (\ix => f (FS ix))

public export
(++) : (axs : All p xs) -> (ays : All p ys) -> All p (xs ++ ys)
[] ++ ays = ays
(ax :: axs) ++ ays = ax :: (axs ++ ays)

public export
splitAt : (n : Nat) ->
          {xs : Vect (n + m) a} ->
          (as : All p xs) ->
          (All p (fst $ splitAt {m} n xs), All p (snd $ splitAt {m} n xs))
splitAt 0 as = ([], as)
splitAt (S n) {xs = _ :: xs} (a :: as) with (splitAt n as) | (splitAt n xs)
  _ | (asn, asm) | (xsn, xsm) = (a :: asn, asm)
