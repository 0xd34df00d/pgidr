module Postgres.Typed.Operations.Expression

import Data.Vect
import Data.Vect.Quantifiers

import public Postgres.Typed.Tuple

%default total
%prefix_record_projections off

public export
data BinRelOp : (ety : Type) -> Type where
  Eq, Gt, Geq, Lt, Leq : BinRelOp ety
  And, Or : BinRelOp Bool

opToSql : BinRelOp ety -> String
opToSql = \case Eq => "="
                Gt => ">"
                Geq => ">="
                Lt => "<"
                Leq => "<="
                And => "AND"
                Or => "OR"

public export
data PgConst : Type -> Type where
  PCString : (str : String) -> PgConst String
  PCNum    : (Show a, Num a) => (num : a) -> PgConst a
  PCBool   : (b : Bool) -> PgConst Bool
  -- TODO there's more! https://www.postgresql.org/docs/current/sql-syntax-lexical.html#SQL-SYNTAX-CONSTANTS

export
valueOf : PgConst ty -> ty
valueOf (PCString str) = str
valueOf (PCNum num) = num
valueOf (PCBool b) = b

public export
data Expr : (0 rowTy : a) -> (ety : Type) -> Type where
  EConst  : (val : PgConst ety) ->
            Expr rowTy ety
  ENone   : Expr rowTy ()

  EAll    : Expr tbl (tableTuple tbl Read)
  EColumn : (sig : Signature qk n) ->
            (ix : Fin n) ->
            Expr rowTy (ix `index` sig).type
  EList   : {0 tys : Vect (S n) Type} ->
            (exprs : All (Expr baseTy) tys) ->
            Expr baseTy (HVect tys)

  EBinRel : (op : BinRelOp ety) ->
            (l, r : Expr rowTy ety) ->
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
  (&&) = EBinRel And
  (||) = EBinRel Or

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
isLeaf (EAll{}) = True
isLeaf (ENone{}) = True
isLeaf (EBinRel{}) = False
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
  toQueryPart (EAll) = "*"
  toQueryPart (ENone) = "NULL"
  toQueryPart (EBinRel op l r) = "\{parens l} \{opToSql op} \{parens r}"
  toQueryPart (ENot e) = "NOT \{parens e}"
  toQueryPart (EList exprs) = joinBy ", " $ go exprs
    where
    go : All (Expr rowTy) tys -> List String
    go [] = []
    go (x :: xs) = toQueryPart x :: go xs

  parens : Expr ty' ret' -> String
  parens e = if isLeaf e then toQueryPart e else "(" ++ toQueryPart e ++ ")"
