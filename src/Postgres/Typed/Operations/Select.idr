module Postgres.Typed.Operations.Select

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple

import Postgres.Typed.Operations.Class
import public Postgres.Typed.Operations.Expression
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
data Order : (ty : Dir -> Type) -> Type where
  ONone : Order ty

public export
record Select (ty : Dir -> Type) (ret : Type) where
  constructor MkSelect
  colCount : Nat
  isTableType : IsRecordType colCount ty -- TODO auto implicit when Idris2#3083 is fixed
  columns : Columns ty ret
  whereClause : Expr ty Bool
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
select _ ty f = f (MkSelect _ %search CAll (1 == 1) ONone)

export
{ty, ret : _} -> Operation (Select ty ret) where
  returnType _ = List ret
  execute conn (MkSelect _ _ columns whereClause orderby) = do
    let query = "SELECT \{joinBy "," $ toColumnNames columns} " ++
                "FROM \{tableNameOf ty} " ++
                "WHERE \{toQueryPart whereClause}"
    result <- execParams' conn query []
    checkQueryStatus result
    let rows = Data.Vect.Fin.tabulate {len = ntuples result} id
    case columns of
         CAll => do matches <- ensureMatches {numRows = ntuples result}
                    map toList $ for rows $ \row => fromRawTuple <$> extractFields result row _ matches
         CSome ixes => do matches <- ensureMatches {numRows = ntuples result}
                          map toList $ for rows $ \row => extractFields result row _ matches
