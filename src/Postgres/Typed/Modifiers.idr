module Postgres.Typed.Modifiers

import Data.String

import Postgres.Typed.PgType
import Postgres.Typed.Signature

%default total
%prefix_record_projections off

public export
Show ty => Show (Modifier ty) where
  show (PKey sort) = case sort of
                          PKeyNormal => "PRIMARY KEY"
                          PKeySerial => "SERIAL PRIMARY KEY"
  show (References other idx) = "REFERENCES \{tableNameOf other} (\{(idx `index` signatureOf other).name})"
  show (Default defVal) = "DEFAULT " ++ show defVal
  show NotNull = "NOT NULL"

public export
isNotNull : Modifier ty -> Bool
isNotNull NotNull = True
isNotNull _ = False

public export
isSerial : Modifier ty -> Bool
isSerial (PKey PKeySerial) = True
isSerial _ = False

public export
isDefaulted : Modifier ty -> Bool
isDefaulted (Default _) = True
isDefaulted _ = False
