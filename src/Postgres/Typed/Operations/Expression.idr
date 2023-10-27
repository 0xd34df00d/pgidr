module Postgres.Typed.Operations.Expression

import Data.Vect
import Data.Vect.Quantifiers

import public Postgres.Typed.InSignature
import Postgres.Typed.Tuple

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
  -- TODO there's more! https://www.postgresql.org/docs/current/sql-syntax-lexical.html#SQL-SYNTAX-CONSTANTS

public export
data Expr : (0 ty : Dir -> Type) -> (ety : Type) -> Type where
  EConst  : (val : PgConst ety) ->
            Expr ty ety
  EColumn : HasSignature n ty =>
            (ix : Fin n) ->
            Expr ty (ix `index` signatureOf ty).type
  EBinRel : (op : BinRelOp) ->
            (l, r : Expr ty ety) ->
            Expr ty Bool

  EAnd : (l, r : Expr ty Bool) ->
         Expr ty Bool
  EOr  : (l, r : Expr ty Bool) ->
         Expr ty Bool
  ENot : (e : Expr ty Bool) -> Expr ty Bool
  -- TODO there's more! https://www.postgresql.org/docs/current/sql-expressions.html

namespace EDSL
  infix 6 ==, <=, >=, <, >
  public export
  (==), (<=), (>=), (<), (>) : (l, r : Expr ty ety) -> Expr ty Bool
  (==) = EBinRel Eq
  (<=) = EBinRel Leq
  (>=) = EBinRel Geq
  (<) = EBinRel Lt
  (>) = EBinRel Gt

  public export
  fromInteger : Integer -> Expr ty Integer
  fromInteger = EConst . PCNum

  public export
  FromString (Expr ty String) where
    fromString = EConst . PCString

  public export
  col : HasSignature n ty =>
        (name : String) ->
        {auto inSig : name `InSignature` signatureOf ty} ->
        Expr ty (anyToFin inSig `index` signatureOf ty).type
  col _ = EColumn (anyToFin inSig)

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
  toQueryPart (EColumn ix) = (ix `index` signatureOf ty).name
  toQueryPart (EBinRel op l r) = "\{parens l} \{opToSql op} \{parens r}"
  toQueryPart (EAnd l r) = "\{parens l} AND \{parens r}"
  toQueryPart (EOr l r) = "\{parens l} OR \{parens r}"
  toQueryPart (ENot e) = "NOT \{parens e}"

  parens : Expr ty' ret' -> String
  parens e = if isLeaf e then toQueryPart e else "(" ++ toQueryPart e ++ ")"
