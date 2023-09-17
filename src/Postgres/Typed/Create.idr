module Postgres.Typed.Create

import public Data.Vect.Quantifiers

import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.PgType
import Postgres.Typed.Tuple

%default total

nullStr : Nullability -> String
nullStr Nullable = ""
nullStr NonNullable = "NOT NULL"

fieldStr : (se : SignatureElem) ->
           CreatablePgType (se.type) =>
           String
fieldStr (MkSE name type isNull) = "\{name} \{fieldTypeNameOf type} \{nullStr isNull}"

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
createQuery : (ty : Type) ->
              IsTableType _ ty =>
              All (CreatablePgType . (.type)) (signatureOf ty) ->
              String
createQuery ty creatables = "CREATE TABLE \{tableNameOf ty} (\{fieldsStr _ creatables})"

export
create : HasIO io =>
         Conn s ->
         (ty : Type) ->
         IsTableType _ ty =>
         {alls : All (CreatablePgType . (.type)) (signatureOf ty)} ->
         io (Either String ())
create conn ty = do
  res <- exec conn $ createQuery ty alls
  status <- resultStatus res
  case status of
       CommandOk => pure $ pure ()
       _ => Left <$> resultErrorMessage res
