module Postgres.Typed.Signature

import public Data.Vect

import Postgres.Typed.PgType

%default total
%prefix_record_projections off

public export
TypeLookup : Type
TypeLookup = Int -> SomePgType

export
defLookup : TypeLookup
defLookup 23 = MkSomePgType Integer
defLookup 25 = MkSomePgType String
defLookup _ = MkSomePgType UnknownPgType


public export
data PKeySort : (ty : Type) -> Type where
  PKeyNormal : PKeySort ty
  PKeySerial : PKeySort Integer

public export
data Modifier : (ty : Type) -> Type

public export
record SignatureElem where
  constructor MkSE
  name : String
  type : Type
  modifiers : List (Modifier type)
  {auto pgType : PgType type}

public export
Signature : Nat -> Type
Signature n = Vect n SignatureElem

public export
interface HasTableName (0 ty : a) where
  tableName : String

public export
tableNameOf : (0 ty : _) ->
              HasTableName ty =>
              String
tableNameOf ty = tableName {ty}

public export
interface HasSignature n (0 ty : a) | ty where
  signature : Signature n

public export
signatureOf : (0 ty : _) ->
              HasSignature n ty =>
              Signature n
signatureOf ty = signature {ty}

public export
data Modifier : (ty : Type) -> Type where
  PKey : PKeySort ty -> Modifier ty
  References : (0 other : Type) ->
               (HasTableName other, HasSignature _ other) =>
               (idx : Fin n) ->
               {auto teq : ty = (idx `index` signatureOf other).type} ->
               Modifier ty
  Default : (defVal : ty) ->
            Modifier ty
  NotNull : Modifier ty

infixl 7 @:, @:?
public export
(@:), (@:?) : (name : String) ->
              (ty : Type) ->
              PgType ty =>
              SignatureElem
name @: ty = MkSE name ty [NotNull]
name @:? ty = MkSE name ty []

public export
Serial : (name : String) ->
         SignatureElem
Serial name = MkSE name Integer [PKey PKeySerial]

public export
subSignature : Signature n ->
               Vect k (Fin n) ->
               Signature k
subSignature sig cols = map (`index` sig) cols

export
columnNames : (0 ty : _) ->
              HasSignature n ty =>
              Vect k (Fin n) ->
              Vect k String
columnNames ty = map (.name . (`index` signatureOf ty))

export
allColumnNames : (0 ty : _) ->
                 HasSignature n ty =>
                 Vect n String
allColumnNames ty = map (.name) $ signatureOf ty
