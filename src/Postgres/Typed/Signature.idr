module Postgres.Typed.Signature

import public Data.Vect
import Data.Vect.Quantifiers

import Postgres.Typed.PgType

%default total
%prefix_record_projections off

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
  constructor MkHasSignature
  signature : Signature n

public export
signatureOf : (0 ty : _) ->
              {auto hasSig : HasSignature n ty} ->
              Signature n
signatureOf ty = signature {ty}

public export
data Modifier : (ty : Type) -> Type where
  PKey : PKeySort ty -> Modifier ty
  References : (0 other : a) ->
               (HasTableName other, HasSignature _ other) =>
               (idx : Fin n) ->
               {auto teq : ty = (idx `index` signatureOf other).type} ->
               Modifier ty
  Default : (defVal : ty) ->
            Modifier ty
  NotNull : Modifier ty

public export
data HasName : SignatureElem -> String -> Type where
  MkHN : PgType type => (name : String) -> HasName (MkSE name type modifiers) name

public export
findName : String -> Signature n -> Maybe (Fin n)
findName name [] = Nothing
findName name (x :: xs) = if x.name == name then Just FZ else FS <$> findName name xs

public export
data IsJust' : Maybe a -> Type where
  ItIsJust' : (v : a) -> IsJust' (Just v)

public export
fromIsJust' : {0 mv : Maybe a} -> IsJust' mv -> a
fromIsJust' (ItIsJust' v) = v

public export
InSignature : String -> Signature n -> Type
InSignature name sig = IsJust' $ findName name sig

{-
This should really read as

inSigToFin : {0 sig : Signature n} ->
             name `InSignature` sig ->
             Fin n

but due to a some inconsistencies of the current Idris unification algo,
we resort to a less specialized and obvious type,
which somehow helps unification though.
-}
public export
inSigToFin : {0 mv : Maybe a} -> IsJust' mv -> a
inSigToFin = fromIsJust'

public export
namesToIxes : HasSignature n ty =>
              {k : _} ->
              {names : Vect k String} ->
              (alls : All (`InSignature` signatureOf ty) names) ->
              Vect k (Fin n)
namesToIxes [] = []
namesToIxes (inSig :: inSigs) = inSigToFin inSig :: namesToIxes inSigs

infixl 7 @:, @:?, @>
public export
(@:), (@:?) : (name : String) ->
              (ty : Type) ->
              PgType ty =>
              SignatureElem
name @: ty = MkSE name ty [NotNull]
name @:? ty = MkSE name ty []

public export
(@>) : (name : String) ->
       (otherTy : a) ->
       (otherName : String) ->
       HasSignature n otherTy =>
       HasTableName otherTy =>
       {auto inSig : otherName `InSignature` signatureOf otherTy} ->
       SignatureElem
(@>) name otherTy otherName = let idx := inSigToFin inSig
                                  pgTy := (idx `index` signatureOf otherTy).pgType
                               in MkSE name _ [References otherTy idx, NotNull]

public export
PKeyInt : (name : String) ->
          SignatureElem
PKeyInt name = MkSE name Integer [PKey PKeySerial]

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
