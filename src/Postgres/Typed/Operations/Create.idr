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
createQuery : (tbl : Table n) ->
              All (CreatablePgType . (.type)) tbl.signature ->
              String
createQuery tbl creatables = "CREATE TABLE \{tbl.name} (\{fieldsStr _ creatables})"

export
create : MonadExec m =>
         (tbl : Table n) ->
         {auto alls : All (CreatablePgType . (.type)) tbl.signature} ->
         m ()
create tbl = do
  let query = createQuery tbl alls
  QueryResult result <- execQuery query
  ensureQuerySuccess query result
