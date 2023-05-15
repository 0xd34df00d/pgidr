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
                       (Int -> (ty ** (PgType ty, ty `∊` u))) ->
                       ReadRawSig ->
                       Signature u
readRawSig2Signature lookup = map $ \(name, typeCode) => let (res ** _) = lookup typeCode in MkSE u name res


data Tuple : Signature u -> Type where
  Nil   : Tuple []
  (::)  : {name : _} ->
          {sig : _} ->
          (val : ty) ->
          PgType ty =>
          ty `∊` u =>
          (rest : Tuple sig) ->
          Tuple (MkSE u name ty :: sig)

Person : Type
Person = Tuple [MkSE DefU "first_name" String, MkSE DefU "last_name" String, MkSE DefU "age" Int]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]
