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


readRawSig2Signature : (Int -> (ty ** PgType ty)) ->
                       ReadRawSig ->
                       Signature
readRawSig2Signature lookup = map $ \(name, typeCode) => let (res ** _) = lookup typeCode in MkSE name res


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
