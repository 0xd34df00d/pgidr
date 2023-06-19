module Postgres.Typed.Schema

import Postgres.C

import public Postgres.Typed.PgType
import public Postgres.Typed.Signature

%default total


ReadRawSig : Type
ReadRawSig = List (String, Int)

parameters {u : Universe}
  TypeLookup : Type
  TypeLookup = Int -> (ty ** noMaybe ty `∊` u)

  resultSig : (lookup : TypeLookup) ->
              (res : Result s) ->
              Signature {u}
  resultSig lookup res = case nfields res of
                              0 => []
                              S lastCol => [ fname res col @:* lookup (ftype res col)
                                           | col <- [0 .. lastCol]
                                           ]

  public export
  data Tuple' : Signature {u} -> Type where
    Nil   : Tuple' []
    (::)  : (val : ty) ->
            noMaybe ty `∊` u =>
            (rest : Tuple' sig) ->
            Tuple' (name @: ty :: sig)

public export
Tuple : Signature {u = DefU} -> Type
Tuple = Tuple'

public export
signatureOf : (ty : Type) -> {s : _} -> (ty = Tuple' {u} s) => Signature {u}
signatureOf _ = s
