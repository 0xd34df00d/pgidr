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
