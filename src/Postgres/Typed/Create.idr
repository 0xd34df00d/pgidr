module Postgres.Typed.Create

import Data.String
import public Data.Vect.Quantifiers

import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.PgType
import Postgres.Typed.Tuple
import Postgres.Typed.Util

%default total

modsStr : Show (Modifier ty) => List (Modifier ty) -> String
modsStr = joinBy " " . map show

fieldStr : (se : SignatureElem) ->
           CreatablePgType (se.type) =>
           String
fieldStr (MkSE name type mods) =
  if isSerial `any` mods
     then "\{name} \{modsStr mods}"
     else "\{name} \{fieldTypeNameOf type} \{modsStr mods}"

fieldsStr : (sig : Signature _) ->
            All (CreatablePgType . (.type)) sig ->
            String
fieldsStr sig alls = concat $ intersperse ", " $ go sig alls
  where
  go : (sig : Signature n) ->
       All (CreatablePgType . (.type)) sig ->
       Vect n String
  go [] [] = []
  go (elem :: eRest) (creatable :: cRest) = fieldStr elem :: go eRest cRest

export
createQuery : (ty : _) ->
              HasSignature _ ty =>
              All (CreatablePgType . (.type)) (signatureOf ty) ->
              String
createQuery ty creatables = "CREATE TABLE \{tableNameOf ty} (\{fieldsStr _ creatables})"

export
create : HasIO io =>
         Conn s ->
         (ty : _) ->
         HasSignature _ ty =>
         {alls : All (CreatablePgType . (.type)) (signatureOf ty)} ->
         io (Either String ())
create conn ty = exec conn (createQuery ty alls) >>= checkStatus
