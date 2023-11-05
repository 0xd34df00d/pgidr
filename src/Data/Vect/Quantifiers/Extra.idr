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
