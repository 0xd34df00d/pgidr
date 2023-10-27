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
tabulate : {n : _} -> {0 xs : Vect n _} -> (Fin n -> ty) -> All (const ty) {n} xs
tabulate {xs = []} f = []
tabulate {xs = _ :: _} f = f FZ :: tabulate (f . FS)
