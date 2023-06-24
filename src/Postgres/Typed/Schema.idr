module Postgres.Typed.Schema

import Postgres.C

import public Postgres.Typed.PgType
import public Postgres.Typed.Signature

%default total

public export
data Tuple' : {u : Universe} -> Signature {u} -> Type where
  Nil   : Tuple' []
  (::)  : (val : ty) ->
          noMaybe ty `∊` u =>
          (rest : Tuple' {u} sig) ->
          Tuple' {u} (name @: ty :: sig)

TypeLookup : {u : Universe} -> Type
TypeLookup = Int -> (ty ** noMaybe ty `∊` u)

parameters {u : Universe} (lookup : TypeLookup {u})
  resultSig'go : (res : Result s) ->
                 (rem, col : Nat) ->
                 Signature {u}
  resultSig'go res Z _ = []
  resultSig'go res (S n) col = (fname res col @:* lookup (ftype res col)) :: resultSig'go res n (S col)

  resultSig : (res : Result s) ->
              Signature {u}
  resultSig res = resultSig'go res (nfields res) 0

  convert : (res : Result s) ->
            (row, col : Nat) ->
            (ty : Type) ->
            (prf : noMaybe ty `∊` u) ->
            Either ConvertError ty
  resultAt : (res : Result s) ->
             (row : Nat) ->
             Either ConvertError (Tuple' (resultSig res))
  resultAt res row = go (nfields res) 0
    where
      go : (rem : Nat) -> (col : Nat) -> Either ConvertError (Tuple' (resultSig'go res rem col))
      go Z _ = pure []
      go (S n) col with (lookup $ ftype res col)
        _ | (ty ** prf) = do val <- convert res row col ty prf
                             rest <- go n (S col)
                             pure $ val :: rest

  resultSet : (res : Result s) ->
              List (Either ConvertError (Tuple' (resultSig res)))
  resultSet res = case ntuples res of
                       0 => []
                       S lastRow => [ resultAt res row | row <- [0 .. lastRow] ]

public export
Tuple : Signature {u = DefU} -> Type
Tuple = Tuple'

public export
signatureOf : (ty : Type) -> {s : _} -> (ty = Tuple' {u} s) => Signature {u}
signatureOf _ = s
