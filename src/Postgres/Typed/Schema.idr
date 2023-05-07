module Postgres.Typed.Schema

import Postgres.C

%default total
%prefix_record_projections off

record UnknownPgType where
  constructor MkUPT
  rawContents : String

interface PgType ty where
  toTextual : ty -> String
  fromTextual : String -> Either String ty

PgType String where
  toTextual = id
  fromTextual = pure

PgType Int where
  toTextual = cast
  fromTextual = pure . cast -- TODO better error reporting

PgType UnknownPgType where
  toTextual = .rawContents
  fromTextual = pure . MkUPT

data SignatureElem : Type where
  MkSE : (name : String) ->
         (ty : Type) ->
         {auto pgType : PgType ty} ->
         SignatureElem

Signature : Type
Signature = List SignatureElem

data Tuple : Signature -> Type where
  Nil   : Tuple []
  (::)  : {name : _} ->
          {sig : _} ->
          (val : ty) ->
          {auto pgType : PgType ty} ->
          (rest : Tuple sig) ->
          Tuple (MkSE name ty :: sig)

Person : Type
Person = Tuple [MkSE "first_name" String, MkSE "last_name" String, MkSE "age" Int]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]
