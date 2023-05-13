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


ReadRawSig : Type
ReadRawSig = List (String, Int)

resultSig : HasIO io =>
            (res : Result s) ->
            io ReadRawSig
resultSig res = do
  cols <- nfields res
  forTo 0 cols $ \col => (,) <$> fname res col <*> ftype res col


data SignatureElem : Type where
  MkSE : (name : String) ->
         (ty : Type) ->
         {auto pgType : PgType ty} ->
         SignatureElem

Signature : Type
Signature = List SignatureElem


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
