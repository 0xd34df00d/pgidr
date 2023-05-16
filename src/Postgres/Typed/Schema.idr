module Postgres.Typed.Schema

import Postgres.C

import Postgres.Typed.PgType
import Postgres.Typed.Signature

%default total


ReadRawSig : Type
ReadRawSig = List (String, Int)

resultSig : HasIO io =>
            (res : Result s) ->
            io ReadRawSig
resultSig res = do
  cols <- nfields res
  forTo 0 cols $ \col => (,) <$> fname res col <*> ftype res col


readRawSig2Signature : {u : Universe} ->
                       (lookup : Int -> (ty ** (PgType ty, ty `∊` u))) ->
                       ReadRawSig ->
                       Signature {u}
readRawSig2Signature lookup =
  map $ \(name, typeCode) => let (ty ** _) = lookup typeCode in field {u} name ty


data Tuple : {u : Universe} -> Signature {u} -> Type where
  Nil   : Tuple []
  (::)  : (val : ty) ->
          PgType ty =>
          ty `∊` u =>
          (rest : Tuple sig) ->
          Tuple (field {u} name ty :: sig)

Person : Type
Person = Tuple ["first_name" @: String, "last_name" @: String, "age" @: Int]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]

Person' : Type
Person' = Tuple ["first_name" @: String, "last_name" @: String, "age" @: Int]
