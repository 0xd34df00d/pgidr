module Postgres.Typed.Util

import Data.Vect.Quantifiers

import Postgres.C

import Postgres.Typed.Signature

%default total

public export
record Dummy (tag : Type) where
  constructor MkDF

export
columnNames : Signature n ->
              Vect k (Fin n) ->
              Vect k String
columnNames sig = map (.name . (`index` sig))

export
allColumnNames : Signature n ->
                 Vect n String
allColumnNames = map (.name)

export
mapProperty' : {xs : Vect n a} ->
               (f : (x : a) -> p x -> q x) ->
               All p xs ->
               All q xs
mapProperty' f [] = []
mapProperty' f (x :: xs) = f _ x :: mapProperty' f xs

export
traverseProperty : Applicative f =>
                   {xs : Vect n a} ->
                   (forall x. p x -> f (q x)) ->
                   All p xs ->
                   f (All q xs)
traverseProperty f [] = pure []
traverseProperty f (x :: xs) = [| f x :: traverseProperty f xs |]

export
traverseProperty' : Applicative f =>
                    {xs : Vect n a} ->
                    ((x : a) -> p x -> f (q x)) ->
                    All p xs ->
                    f (All q xs)
traverseProperty' f [] = pure []
traverseProperty' f (x :: xs) = [| f _ x :: traverseProperty' f xs |]

export
tabulate : {n : _} -> {0 xs : Vect n _} -> (Fin n -> ty) -> All (const ty) {n} xs
tabulate {xs = []} f = []
tabulate {xs = _ :: _} f = f FZ :: tabulate (f . FS)
