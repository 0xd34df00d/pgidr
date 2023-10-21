module Postgres.Typed.Operations.Select

import Data.String

import Postgres.C

import public Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class

%default total
%prefix_record_projections off

namespace Output
  public export
  data Columns : (0 ty : Dir -> Type) -> (0 ret : Type) -> Type where
    CAll    : HasSignature n ty => Columns ty (ty Read)
    CSome   : HasSignature n ty =>
              (ixes : Vect k (Fin n)) ->
              Columns ty (subTuple ty ixes Read)

  export
  toColumnNames : Columns ty ret ->
                  List String
  toColumnNames CAll = toList $ allColumnNames ty
  toColumnNames (CSome ixes) = toList $ columnNames ty ixes

public export
data Order : (ty : Dir -> Type) -> Type where
  ONone : Order ty

public export
record Select (ty : Dir -> Type) (ret : Type) where
  constructor MkSelect
  isTableType : HasSignature colCount ty
  columns : Columns ty ret
  orderby : Order ty

data DFrom : Type where
public export
from : Dummy DFrom
from = MkDF

public export
select : Dummy DFrom ->
         (ty : Dir -> Type) ->
         HasSignature n ty =>
         (Select ty (ty Read) -> Select ty ret) ->
         Select ty ret
select _ ty f = f (MkSelect %search CAll ONone)

export
{ty, ret : _} -> Operation (Select ty ret) where
  returnType _ = List ret
  execute conn (MkSelect _ columns orderby) = do
    let query = "SELECT \{joinBy "," $ toColumnNames columns} FROM \{tableNameOf ty}"
    result <- execParams' conn query []
    checkQueryStatus result
    pure ?executeRhs
