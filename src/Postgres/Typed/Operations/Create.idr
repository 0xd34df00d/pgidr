module Postgres.Typed.Operations.Create

import Data.String
import public Data.Vect.Quantifiers

import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.PgType
import Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class

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
fieldsStr sig alls = joinBy ", " $ toList $ forget $ mapProperty' fieldStr alls

export
createQuery : (ty : _) ->
              HasSignature _ ty =>
              All (CreatablePgType . (.type)) (signatureOf ty) ->
              String
createQuery ty creatables = "CREATE TABLE \{tableNameOf ty} (\{fieldsStr _ creatables})"

export
create : MonadExec m =>
         Conn s ->
         (ty : _) ->
         HasSignature _ ty =>
         {auto alls : All (CreatablePgType . (.type)) (signatureOf ty)} ->
         m ()
create conn ty = exec conn (createQuery ty alls) >>= checkQueryStatus
