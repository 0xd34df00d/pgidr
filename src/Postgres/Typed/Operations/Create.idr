module Postgres.Typed.Operations.Create

import Data.String
import public Data.Vect.Quantifiers

import Data.Vect.Quantifiers.Extra

import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.PgType
import Postgres.Typed.Tuple

import Postgres.Typed.Operations.Class

%default total

modsStr : Show (Modifier ty) => List (Modifier ty) -> String
modsStr = joinBy " " . map show

fieldStr : (se : SignatureElem Unqualified) ->
           CreatablePgType (se.type) =>
           String
fieldStr (MkSE name type mods) =
  if isSerial `any` mods
     then "\{name} \{modsStr mods}"
     else "\{name} \{fieldTypeNameOf type} \{modsStr mods}"

fieldsStr : (sig : Signature Unqualified _) ->
            All (CreatablePgType . (.type)) sig ->
            String
fieldsStr sig alls = joinBy ", " $ toList $ forget $ mapPropertyRelevant fieldStr alls

export
createQuery : (ty : _) ->
              (HasSignature Unqualified _ ty, HasTableName ty) =>
              All (CreatablePgType . (.type)) (signatureOf ty) ->
              String
createQuery ty creatables = "CREATE TABLE \{tableNameOf ty} (\{fieldsStr _ creatables})"

export
create : MonadExec m =>
         Conn s ->
         (ty : _) ->
         (HasSignature Unqualified _ ty, HasTableName ty) =>
         {auto alls : All (CreatablePgType . (.type)) (signatureOf ty)} ->
         m ()
create conn ty = let query = createQuery ty alls
                  in exec conn query >>= checkQueryStatus query
