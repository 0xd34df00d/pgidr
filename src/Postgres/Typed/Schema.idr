module Postgres.Typed.Schema

import Postgres.C

import public Postgres.Typed.Tuple

%default total

public export
nullable : (res : Result s) -> (col : ColI res) -> Nullability
nullable res col = if fnullable res col then Nullable else NonNullable

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


parameters (lookup : TypeLookup)
  resultSig : (res : Result s) ->
              (nulls : ColumnNullables res) ->
              Signature (nfields res)
  resultSig res nulls =
    let types = ftype `onColumns` res
        names = fname `onColumns` res
        f : Int -> String -> Nullability -> SignatureElem
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

  resultAtRow' : (res : Result s) ->
                 (row : RowI res) ->
                 (cols : Vect ncols (Fin (nfields res))) ->
                 (sig : Signature ncols) ->
                 Either ConvertError (Tuple sig)
  resultAtRow' res row = go
    where
    go : Vect n (Fin (nfields res)) ->
         (sig : Signature n) ->
         Either ConvertError (Tuple sig)
    go [] [] = pure []
    go (col :: cols) (MkSE _ ty isNull :: sigs) = (::)
                                              <$> convert res row col ty isNull
                                              <*> go cols sigs

  resultAtRow : (res : Result s) ->
                (sig : Signature (nfields res)) ->
                (row : RowI res) ->
                Either ConvertError (Tuple sig)
  resultAtRow res sig row = resultAtRow' res row range sig

  export
  resultSet : (res : Result s) ->
              Vect (ntuples res) (Either ConvertError (Tuple (resultSig res (collectNullables res))))
  resultSet res with (resultSig res (collectNullables res))
    _ | sig = resultAtRow res sig <$> range
