module Postgres.Typed.Signature

import public Data.Vect
import Data.Vect.Quantifiers

import Postgres.Typed.PgType

%default total
%prefix_record_projections off

public export
data QualKind = Qualified | Unqualified

public export
record QualifiedName where
  constructor MkQN
  qualifier : String
  qname : String

public export 0
Name : (0 qk : QualKind) -> Type
Name Unqualified = String
Name Qualified = QualifiedName


public export
data PKeySort : (ty : Type) -> Type where
  PKeyNormal : PKeySort ty
  PKeySerial : PKeySort Integer

public export
data Modifier : (ty : Type) -> Type

public export
record SignatureElem (qk : QualKind) where
  constructor MkSE
  name : Name qk
  type : Type
  modifiers : List (Modifier type)
  {auto pgType : PgType type}

public export
Signature : (qk : QualKind) -> (n : Nat) -> Type
Signature qk n = Vect n (SignatureElem qk)

public export
interface HasTableName (0 ty : a) where
  tableName : String

public export
tableNameOf : (0 ty : _) ->
              HasTableName ty =>
              String
tableNameOf ty = tableName {ty}

public export
interface HasSignature qk n (0 ty : a) | ty where
  constructor MkHasSignature
  signature : Signature qk n

public export
signatureOf : (0 ty : _) ->
              {auto hasSig : HasSignature qk n ty} ->
              Signature qk n
signatureOf ty = signature {ty}

public export
data Modifier : (ty : Type) -> Type where
  PKey : PKeySort ty -> Modifier ty
  References : (0 other : a) ->
               (HasTableName other, HasSignature Unqualified _ other) =>
               (idx : Fin n) ->
               {auto teq : ty = (idx `index` signatureOf other).type} ->
               Modifier ty
  Default : (defVal : ty) ->
            Modifier ty
  NotNull : Modifier ty

public export
-- TODO generalize
findName : String -> Signature Unqualified n -> Maybe (Fin n)
findName name [] = Nothing
findName name (x :: xs) = if x.name == name then Just FZ else FS <$> findName name xs

public export
data IsJust' : Maybe a -> Type where
  ItIsJust' : (v : a) -> IsJust' (Just v)

public export
fromIsJust' : {0 mv : Maybe a} -> IsJust' mv -> a
fromIsJust' (ItIsJust' v) = v

public export
InSignature : String -> Signature Unqualified n -> Type
InSignature name sig = IsJust' $ findName name sig

{-
This should really read as

inSigToFin : {0 sig : Signature qk n} ->
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
namesToIxes : HasSignature Unqualified n ty =>
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
              SignatureElem Unqualified
name @: ty = MkSE name ty [NotNull]
name @:? ty = MkSE name ty []

public export
(@>) : (name : String) ->
       (otherTy : a) ->
       (otherName : String) ->
       HasSignature Unqualified n otherTy =>
       HasTableName otherTy =>
       {auto inSig : otherName `InSignature` signatureOf otherTy} ->
       SignatureElem Unqualified
(@>) name otherTy otherName = let idx := inSigToFin inSig
                                  pgTy := (idx `index` signatureOf otherTy).pgType
                               in MkSE name _ [References otherTy idx, NotNull]

public export
PKeyInt : (name : String) ->
          SignatureElem Unqualified
PKeyInt name = MkSE name Integer [PKey PKeySerial]

public export
subSignature : Signature qk n ->
               Vect k (Fin n) ->
               Signature qk k
subSignature sig cols = map (`index` sig) cols

export
columnNames : (0 ty : _) ->
              HasSignature qk n ty =>
              Vect k (Fin n) ->
              Vect k (Name qk)
columnNames ty = map (.name . (`index` signatureOf ty))

export
allColumnNames : (0 ty : _) ->
                 HasSignature qk n ty =>
                 Vect n (Name qk)
allColumnNames ty = map (.name) $ signatureOf ty
