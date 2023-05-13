module Postgres.Typed.Signature

import Postgres.Typed.PgType

%default total

public export
data SignatureElem : Type where
  MkSE : (name : String) ->
         (ty : Type) ->
         {auto pgType : PgType ty} ->
         SignatureElem

public export
Signature : Type
Signature = List SignatureElem
