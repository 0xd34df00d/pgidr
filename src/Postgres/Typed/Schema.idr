module Postgres.Typed.Schema

import Postgres.C

%default total

%prefix_record_projections off
record SignatureElem where
  constructor MkSE
  name : String
  ty : Type

Signature : Type
Signature = List SignatureElem

data Tuple : Signature -> Type where
  Nil   : Tuple []
  (::)  : {name : _} ->
          {sig : _} ->
          (val : ty) ->
          (rest : Tuple sig) ->
          Tuple (MkSE name ty :: sig)

Person : Type
Person = Tuple [MkSE "first_name" String, MkSE "last_name" String, MkSE "age" Int]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]
