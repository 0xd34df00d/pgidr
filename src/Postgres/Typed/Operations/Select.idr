module Postgres.Typed.Operations.Select

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class
import public Postgres.Typed.Operations.Helpers

%default total
%prefix_record_projections off

namespace Output
  public export
  data Columns : (0 ty : Dir -> Type) -> (0 ret : Type) -> Type where
    CAll    : HasSignature n ty => Columns ty (ty Read)
    CSome   : HasSignature n ty =>
              {k : _} ->
              (ixes : Vect k (Fin n)) ->
              Columns ty (subTuple ty ixes Read)

  export
  toColumnNames : Columns ty ret ->
                  List String
  toColumnNames CAll = toList $ allColumnNames ty
  toColumnNames (CSome ixes) = toList $ columnNames ty ixes

namespace Expression
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
    EBinRel : (l, r : Expr ty ety) ->
              (op : BinRelOp) ->
              Expr ty Bool

    EAnd : (l, r : Expr ty Bool) ->
           Expr ty Bool
    EOr  : (l, r : Expr ty Bool) ->
           Expr ty Bool
    ENot : (e : Expr ty Bool) -> Expr ty Bool
    -- TODO there's more! https://www.postgresql.org/docs/current/sql-expressions.html

  Interpolation (Expr ty ret) where
    interpolate (EConst val) = case val of
                                    PCString str => "'\{str}'"
                                    PCNum n => show n
    interpolate (EColumn ix) = (ix `index` signatureOf ty).name
    interpolate (EBinRel l r op) = "\{l} \{opToSql op} \{r}"
    interpolate (EAnd l r) = "\{l} AND \{r}"
    interpolate (EOr l r) = "\{l} OR \{r}"
    interpolate (ENot e) = "NOT \{e}"

  export
  toQueryPart : Expr ty ret -> String
  toQueryPart = interpolate

public export
data Order : (ty : Dir -> Type) -> Type where
  ONone : Order ty

public export
record Select (ty : Dir -> Type) (ret : Type) where
  constructor MkSelect
  colCount : Nat
  isTableType : IsRecordType colCount ty -- TODO auto implicit when Idris2#3083 is fixed
  columns : Columns ty ret
  whereClause : Maybe (Expr ty Bool)
  orderby : Order ty

data DFrom : Type where
public export
from : Dummy DFrom
from = MkDF

public export
select : Dummy DFrom ->
         (ty : Dir -> Type) ->
         {n : _} ->
         IsRecordType n ty =>
         (Select ty (ty Read) -> Select ty ret) ->
         Select ty ret
select _ ty f = f (MkSelect _ %search CAll Nothing ONone)

export
{ty, ret : _} -> Operation (Select ty ret) where
  returnType _ = List ret
  execute conn (MkSelect _ _ columns whereClause orderby) = do
    let wherePart = maybe "" (("WHERE " ++) . toQueryPart) whereClause
        query = "SELECT \{joinBy "," $ toColumnNames columns} " ++
                "FROM \{tableNameOf ty} " ++
                "\{wherePart}"
    result <- execParams' conn query []
    checkQueryStatus result
    let rows = Data.Vect.Fin.tabulate {len = ntuples result} id
    case columns of
         CAll => do matches <- ensureMatches {numRows = ntuples result}
                    map toList $ for rows $ \row => fromRawTuple <$> extractFields result row _ matches
         CSome ixes => do matches <- ensureMatches {numRows = ntuples result}
                          map toList $ for rows $ \row => extractFields result row _ matches
