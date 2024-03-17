module Postgres.Typed.Operations.Expression

import Data.Vect
import Data.Vect.Quantifiers

import public Postgres.Typed.Tuple

%default total
%prefix_record_projections off

public export
data BinRelOp = Eq | Gt | Geq | Lt | Leq

opToSql : BinRelOp -> String
opToSql = \case Eq => "="
                Gt => ">"
                Geq => ">="
                Lt => "<"
                Leq => "<="

public export
data PgConst : Type -> Type where
  PCString : String -> PgConst String
  PCNum    : (Show a, Num a) => a -> PgConst a
  PCBool   : Bool -> PgConst Bool
  -- TODO there's more! https://www.postgresql.org/docs/current/sql-syntax-lexical.html#SQL-SYNTAX-CONSTANTS

public export
data Expr : (0 ty : a) -> (ety : Type) -> Type where
  EConst  : (val : PgConst ety) ->
            Expr ty ety
  EColumn : (sig : Signature qk n) ->
            (ix : Fin n) ->
            Expr ty (ix `index` sig).type
  EBinRel : (op : BinRelOp) ->
            (l, r : Expr ty ety) ->
            Expr ty Bool

  EAnd : (l, r : Expr ty Bool) ->
         Expr ty Bool
  EOr  : (l, r : Expr ty Bool) ->
         Expr ty Bool
  ENot : (e : Expr ty Bool) -> Expr ty Bool
  -- TODO there's more! https://www.postgresql.org/docs/current/sql-expressions.html

namespace IntegerVal
  public export
  val : Integer -> Expr ty Integer
  val = EConst . PCNum

namespace EDSL
  infix 6 ==, <=, >=, <, >
  public export
  (==), (<=), (>=), (<), (>) : (l, r : Expr ty ety) -> Expr ty Bool
  (==) = EBinRel Eq
  (<=) = EBinRel Leq
  (>=) = EBinRel Geq
  (<) = EBinRel Lt
  (>) = EBinRel Gt

  infix 5 &&, ||
  public export
  (&&), (||) : (l, r : Expr ty Bool) -> Expr ty Bool
  (&&) = EAnd
  (||) = EOr

  public export
  fromInteger : Integer -> Expr ty Integer
  fromInteger = EConst . PCNum

  public export
  FromString (Expr ty String) where
    fromString = EConst . PCString

  public export
  col : (name : Name qk) ->
        {sig : Signature qk _} ->
        {auto inSig : name `InSignature` sig} ->
        Expr sig (inSigToFin inSig `index` sig).type
  col _ = EColumn sig (inSigToFin inSig)

  infix 9 .!.
  public export
  (.!.) : (qual, name : String) ->
        {sig : Signature Qualified _} ->
        {auto inSig : QName qual name `InSignature` sig} ->
        Expr sig (inSigToFin inSig `index` sig).type
  (.!.) _ _ = EColumn sig (inSigToFin inSig)

isLeaf : Expr ty ety -> Bool
isLeaf (EConst{}) = True
isLeaf (EColumn{}) = True
isLeaf (EBinRel{}) = False
isLeaf (EAnd{}) = False
isLeaf (EOr{}) = False
isLeaf (ENot{}) = False

mutual
  export
  toQueryPart : Expr ty ret -> String
  toQueryPart (EConst val) = case val of
                                  PCString str => "'\{str}'"
                                  PCNum n => show n
                                  PCBool b => case b of
                                                   True => "TRUE"
                                                   False => "FALSE"
  toQueryPart (EColumn sig ix) = showName (ix `index` sig).name
  toQueryPart (EBinRel op l r) = "\{parens l} \{opToSql op} \{parens r}"
  toQueryPart (EAnd l r) = "\{parens l} AND \{parens r}"
  toQueryPart (EOr l r) = "\{parens l} OR \{parens r}"
  toQueryPart (ENot e) = "NOT \{parens e}"

  parens : Expr ty' ret' -> String
  parens e = if isLeaf e then toQueryPart e else "(" ++ toQueryPart e ++ ")"
