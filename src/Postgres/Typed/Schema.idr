module Postgres.Typed.Schema

import Postgres.C

import public Postgres.Typed.PgType
import public Postgres.Typed.Signature

%default total


ReadRawSig : Type
ReadRawSig = List (String, Int)

resultRawSig : (res : Result s) ->
               ReadRawSig
resultRawSig res = [ (fname res col, ftype res col) | col <- [0 .. nfields res] ]

parameters {u : Universe}
  TypeLookup : Type
  TypeLookup = Int -> (ty ** noMaybe ty `∊` u)

  readRawSig2Signature : (lookup : TypeLookup) ->
                         ReadRawSig ->
                         Signature {u}
  readRawSig2Signature lookup =
    map $ \(name, typeCode) => let (ty ** _) = lookup typeCode in
                                   name @: ty

  public export
  data Tuple' : Signature {u} -> Type where
    Nil   : Tuple' []
    (::)  : (val : ty) ->
            noMaybe ty `∊` u =>
            (rest : Tuple' sig) ->
            Tuple' (name @: ty :: sig)

public export
Tuple : Signature {u = DefU} -> Type
Tuple = Tuple'

public export
signatureOf : (ty : Type) -> {s : _} -> (ty = Tuple' {u} s) => Signature {u}
signatureOf _ = s

Person : Type
Person = Tuple ["first_name" @: String, "last_name" @: String, "age" @: Integer]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]

Person' : Type
Person' = Tuple ["first_name" @: String, "last_name" @: String, "age" @: Maybe Integer]

sampleName' : Person'
sampleName' = [ "John", "Doe", Just 42 ]
