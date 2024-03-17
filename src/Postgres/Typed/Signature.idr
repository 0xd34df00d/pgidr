module Postgres.Typed.Signature

import public Data.String
import public Data.List1
import public Data.Vect
import Data.Vect.Quantifiers

import Postgres.Typed.PgType

%default total
%prefix_record_projections off

public export
data QualKind = Qualified | Unqualified

public export
data Name : (qk : QualKind) -> Type where
  UName : (name : String) -> Name Unqualified
  QName : (qualifier, qname : String) -> Name Qualified

public export
(.uname) : Name Unqualified -> String
(.uname) (UName n) = n

public export
Eq (Name qk) where
  UName n1 == UName n2 = n1 == n2
  QName q1 n1 == QName q2 n2 = q1 == q2 && n1 == n2

export
showName : Name qk -> String
showName (UName name) = name
showName (QName qualifier qname) = qualifier ++ "." ++ qname

export
Interpolation (Name qk) where
  interpolate = showName

namespace UNFS
  public export
  fromString : (str : String) -> Name Unqualified
  fromString = UName

namespace QNFS
  public export 0
  ValidQualifiedString : String -> Type
  ValidQualifiedString str = length (split (== '.') str) = 2

  public export
  fromString : (str : String) ->
               ValidQualifiedString str =>
               Name Qualified
  fromString str = let qual ::: [name] = split (== '.') str
                    in QName qual name

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
  0 type : Type
  modifiers : List (Modifier type)
  {auto pgType : PgType type}

public export 0
Signature : (qk : QualKind) -> (n : Nat) -> Type
Signature qk n = Vect n (SignatureElem qk)

public export
record Table ncols where
  constructor MkTable
  name : String
  signature : Signature Unqualified ncols

public export
data Modifier : (ty : Type) -> Type where
  PKey : PKeySort ty -> Modifier ty
  References : (other : Table n) ->
               (idx : Fin n) ->
               {auto teq : ty = (idx `index` other.signature).type} ->
               Modifier ty
  Default : (defVal : ty) ->
            Modifier ty
  NotNull : Modifier ty

public export
findName : Name qk -> Signature qk n -> Maybe (Fin n)
findName name [] = Nothing
findName name (x :: xs) = if name == x.name
                             then Just FZ
                             else FS <$> findName name xs

public export
data IsJust' : Maybe a -> Type where
  ItIsJust' : (v : a) -> IsJust' (Just v)

public export
fromIsJust' : {0 mv : Maybe a} -> IsJust' mv -> a
fromIsJust' (ItIsJust' v) = v

public export 0
InSignature : Name qk -> Signature qk n -> Type
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
namesToIxes : {k, n : _} ->
              {0 sig : Signature Unqualified n} ->
              {names : Vect k (Name Unqualified)} ->
              (alls : All (`InSignature` sig) names) ->
              Vect k (Fin n)
namesToIxes [] = []
namesToIxes (inSig :: inSigs) = inSigToFin inSig :: namesToIxes inSigs

infixl 7 @:, @:?, @>
public export
(@:), (@:?) : (name : String) ->
              (0 ty : Type) ->
              PgType ty =>
              SignatureElem Unqualified
name @: ty = MkSE (UName name) ty [NotNull]
name @:? ty = MkSE (UName name) ty []

public export
(@>) : (name : String) ->
       (other : Table n) ->
       (otherName : Name Unqualified) ->
       {auto inSig : otherName `InSignature` other.signature} ->
       SignatureElem Unqualified
(@>) name other otherName =
  let idx := inSigToFin inSig
      pgTy := (idx `index` other.signature).pgType
   in MkSE (UName name) _ [References other idx, NotNull]

public export
PKeyInt : (name : String) ->
          SignatureElem Unqualified
PKeyInt name = MkSE (UName name) Integer [PKey PKeySerial]

public export
subSignature : Signature qk n ->
               Vect k (Fin n) ->
               Signature qk k
subSignature sig cols = map (`index` sig) cols

export
columnNames : (sig : Signature qk n) ->
              Vect k (Fin n) ->
              Vect k (Name qk)
columnNames sig = map (.name . (`index` sig))

export
allColumnNames : (sig : Signature qk n) ->
                 Vect n (Name qk)
allColumnNames = map (.name)
