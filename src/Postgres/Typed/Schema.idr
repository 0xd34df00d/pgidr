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
  map $ \(name, typeCode) => let (ty ** _) = lookup typeCode in field name ty


data Tuple' : (u : Universe) -> Signature {u} -> Type where
  Nil   : Tuple' u []
  (::)  : (val : ty) ->
          PgType ty =>
          ty `∊` u =>
          (rest : Tuple' u sig) ->
          Tuple' u (field name ty :: sig)

Tuple : Signature {u = DefU} -> Type
Tuple = Tuple' _

Person : Type
Person = Tuple ["first_name" @: String, "last_name" @: String, "age" @: Int]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]

Person' : Type
Person' = Tuple ["first_name" @: String, "last_name" @: String, "age" @: Int]
