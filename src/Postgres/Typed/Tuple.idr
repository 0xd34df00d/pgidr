module Postgres.Typed.Tuple

import public Postgres.Typed.PgType
import public Postgres.Typed.Signature

%default total

public export
data Tuple : Signature n -> Type where
  Nil   : Tuple []
  (::)  : {isNull, name, sig : _} ->
          PgType ty =>
          (val : applyIsNull isNull ty) ->
          (rest : Tuple sig) ->
          Tuple (MkSE name ty isNull :: sig)

export
Show (Tuple sig) where
  show tup = "(" ++ go True tup ++ ")"
    where
    go : Bool -> Tuple sig' -> String
    go _ [] = ""
    go isFirst ((::) {isNull} {name} val rest) =
      let pref : String = if isFirst then "" else ", "
       in case isNull of
               Nullable => case val of
                                Nothing => pref ++ name ++ " is null" ++ go False rest
                                Just val => pref ++ printVal val
               NonNullable => pref ++ printVal val
      where
      printVal : Show ty => ty -> String
      printVal v = name ++ " = " ++ show v ++ go False rest


public export
interface HasSignature n (0 ty : Type) | ty where
  signature : Signature n

  toTuple : ty -> Tuple signature
  fromTuple : Tuple signature -> ty

  fromToId : (v : ty) ->
             fromTuple (toTuple v) = v
  toFromId : (v : Tuple signature) ->
             toTuple (fromTuple v) = v

public export
{s : Signature n} -> HasSignature n (Tuple s) where
  signature = s

  toTuple = id
  fromTuple = id

  fromToId v = Refl
  toFromId v = Refl

public export
signatureOf : (0 ty : Type) -> HasSignature n ty => Signature n
signatureOf ty = signature {ty}
