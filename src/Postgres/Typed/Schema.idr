module Postgres.Typed.Schema

import Data.Vect
import Data.Vect.Indexed
import Data.Vect.Quantifiers

import Postgres.C

import public Postgres.Typed.PgType
import public Postgres.Typed.Signature

%default total

public export
nullable : (res : Result s) -> (col : ColI res) -> Nullability
nullable res col = if fnullable res col then Nullable else NonNullable

public export
data Tuple' : {u : Universe} -> Signature n {u} -> Type where
  Nil   : Tuple' []
  (::)  : {u, isNull, name : _} ->
          {sig : Signature n {u}} ->
          {auto inPrf : ty `∊` u} ->
          (val : applyIsNull isNull ty) ->
          (rest : Tuple' {u} sig) ->
          Tuple' {u} (MkSE name ty isNull :: sig)

export
Show (Tuple' sig) where
  show tup = "(" ++ go True tup ++ ")"
    where
      go : Bool -> Tuple' sig' -> String
      go _ [] = ""
      go isFirst ((::) {inPrf} {isNull} {name} val rest) =
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
data ConvertError = PgTyParseError PgTyParseError

export
Show ConvertError where
  show (PgTyParseError str) = "Type parse error: " ++ str

ColumnNullables : (res : Result s) -> Type
ColumnNullables res = Vect (nfields res) Nullability

collectNullables : (res : Result s) ->
                   ColumnNullables res
collectNullables res = tabulate (\col => nullable res col)


parameters {u : Universe} (lookup : TypeLookup {u})
  resultSig : (res : Result s) ->
              (nulls : ColumnNullables res) ->
              Signature (nfields res) {u}
  resultSig res nulls =
    let types = ftype `onColumns` res
        names = fname `onColumns` res
        f : Int -> String -> Nullability -> SignatureElem {u}
        f = \tyCode, name, nullable => let (ty ** _) = lookup tyCode
                                        in MkSE name ty nullable
     in zipWith3 f types names nulls

  convert : (res : Result s) ->
            (row : RowI res) ->
            (col : ColI res) ->
            (ty : Type) ->
            PgType ty =>
            (isNull : Nullability) ->
            Either ConvertError (applyIsNull isNull ty)
  convert res row col ty isNull =
    let text = getvalueTextual res row col in
    case isNull of
         NonNullable => mapFst PgTyParseError $ fromTextual text
         Nullable => if getisnull res row col
                        then pure Nothing
                        else bimap PgTyParseError Just $ fromTextual text

  resultAt : (res : Result s) ->
             (sig : Signature (nfields res) {u}) ->
             (row : RowI res) ->
             Either ConvertError (Tuple' sig)
  resultAt res sig row = go range sig
    where
      go : Vect n (Fin (nfields res)) ->
           (sig : Signature n {u}) ->
           Either ConvertError (Tuple' sig)
      go [] [] = pure []
      go (col :: cols) (MkSE _ ty isNull :: sigs)
        = do val <- convert res row col ty isNull
             rest <- go cols sigs
             pure $val :: rest

{-
  public export
  fullResultSet : (res : Result s) ->
                  List (Either ConvertError (Tuple' (resultSig res)))
  fullResultSet res = case ntuples res of
                           0 => []
                           S lastRow => [ resultAt res row | row <- [0 .. lastRow] ]

public export
Tuple : Signature {u = DefU} -> Type
Tuple = Tuple'

public export
signatureOf : (ty : Type) -> {s : _} -> (ty = Tuple' {u} s) => Signature {u}
signatureOf _ = s
-}
