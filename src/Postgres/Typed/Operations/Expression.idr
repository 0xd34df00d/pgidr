module Postgres.Typed.Operations.Expression

import Data.List.Quantifiers
import Data.Vect

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
data Expr : (0 rowTy : a) -> (ety : Type) -> Type where
  EConst  : (val : PgConst ety) ->
            Expr rowTy ety
  EColumn : (sig : Signature qk n) ->
            (ix : Fin n) ->
            Expr rowTy (ix `index` sig).type
  EBinRel : (op : BinRelOp) ->
            (l, r : Expr rowTy ety) ->
            Expr rowTy Bool
  EList   : {0 tys : List Type} ->
            (exprs : All (Expr baseTy) tys) ->
            Expr baseTy (HList tys)

  EAnd : (l, r : Expr rowTy Bool) ->
         Expr rowTy Bool
  EOr  : (l, r : Expr rowTy Bool) ->
         Expr rowTy Bool
  ENot : (e : Expr rowTy Bool) ->
         Expr rowTy Bool
  -- TODO there's more! https://www.postgresql.org/docs/current/sql-expressions.html

namespace IntegerVal
  public export
  val : Integer -> Expr rowTy Integer
  val = EConst . PCNum

namespace StringVal
  public export
  val : String -> Expr rowTy String
  val = EConst . PCString

namespace BoolVal
  public export
  val : Bool -> Expr rowTy Bool
  val = EConst . PCBool

namespace EDSL
  infix 6 ==, <=, >=, <, >
  public export
  (==), (<=), (>=), (<), (>) : (l, r : Expr rowTy ety) -> Expr rowTy Bool
  (==) = EBinRel Eq
  (<=) = EBinRel Leq
  (>=) = EBinRel Geq
  (<) = EBinRel Lt
  (>) = EBinRel Gt

  infix 5 &&, ||
  public export
  (&&), (||) : (l, r : Expr rowTy Bool) -> Expr rowTy Bool
  (&&) = EAnd
  (||) = EOr

  public export
  fromInteger : Integer -> Expr rowTy Integer
  fromInteger = EConst . PCNum

  public export
  FromString (Expr rowTy String) where
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

isLeaf : Expr rowTy ety -> Bool
isLeaf (EConst{}) = True
isLeaf (EColumn{}) = True
isLeaf (EBinRel{}) = False
isLeaf (EAnd{}) = False
isLeaf (EOr{}) = False
isLeaf (ENot{}) = False
isLeaf (EList{}) = False

mutual
  export
  toQueryPart : Expr rowTy ret -> String
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
  toQueryPart (EList exprs) = joinBy ", " $ go exprs
    where
    go : Data.List.Quantifiers.All.All (Expr rowTy) tys -> List String
    go [] = []
    go (x :: xs) = toQueryPart x :: go xs

  parens : Expr ty' ret' -> String
  parens e = if isLeaf e then toQueryPart e else "(" ++ toQueryPart e ++ ")"
