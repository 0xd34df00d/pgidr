module Postgres.Typed.Schema

import Postgres.C

%default total

Signature : Type
Signature = List (String, Type)

data Tuple : Signature -> Type where
  Nil   : Tuple []
  (::)  : {name : _} ->
          {sig : _} ->
          (val : ty) ->
          (rest : Tuple sig) ->
          Tuple ((name, ty) :: sig)

Person : Type
Person = Tuple [("first_name", String), ("last_name", String), ("age", Int)]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]
