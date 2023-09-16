module Postgres.Typed.Create

import public Data.Vect.Quantifiers

import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.PgType
import Postgres.Typed.Tuple

%default total

fieldToString : (se : SignatureElem) ->
                CreatablePgType (se.type) ->
                String
fieldToString (MkSE name type isNull) _ =
  name ++ " " ++ fieldTypeNameOf type ++ case isNull of
                                              Nullable => ""
                                              NonNullable => " NOT NULL"

fieldsToString : (sig : Signature _) ->
                 All (CreatablePgType . (.type)) sig ->
                 String
fieldsToString sig alls = concat $ intersperse ", " $ go sig alls
  where
  go : (sig : Signature n) ->
       All (CreatablePgType . (.type)) sig ->
       Vect n String
  go [] [] = []
  go (elem :: eRest) (creatable :: cRest) = fieldToString elem creatable :: go eRest cRest

export
createQuery : (ty : Type) ->
              IsTableType _ ty =>
              All (CreatablePgType . (.type)) (signatureOf ty) ->
              String
createQuery ty creatables = "CREATE TABLE " ++ tableNameOf ty ++
                            " (" ++ fieldsToString _ creatables ++ ")"

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
