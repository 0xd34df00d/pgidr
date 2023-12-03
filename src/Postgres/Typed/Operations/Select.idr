module Postgres.Typed.Operations.Select

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple

import Postgres.Typed.Operations.Class
import public Postgres.Typed.Operations.Expression
import public Postgres.Typed.Operations.Helpers
import public Postgres.Typed.Operations.SelectSource
import Postgres.Typed.Operations.Join

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

namespace Ordering
  public export
  data OrderDir = Asc | Desc

  orderDirToString : OrderDir -> String
  orderDirToString = \case Asc => "ASC"
                           Desc => "DESC"

  public export
  data NullsPos = First | Last

  nullsPosToString : NullsPos -> String
  nullsPosToString np = "NULLS " ++ case np of
                                         First => "FIRST"
                                         Last => "LAST"

  public export
  record Order (ty : Dir -> Type) where
    constructor MkOrder
    orderExpr : Expr ty a
    direction : Maybe OrderDir
    nulls : Maybe NullsPos

  public export
  fromString : HasSignature n ty =>
               (name : String) ->
               {auto inSig : name `InSignature` signatureOf ty} ->
               Maybe (Order ty)
  fromString name = Just $ MkOrder (col name) Nothing Nothing

  export
  toQueryPart : Order ty ->
                String
  toQueryPart (MkOrder expr dir nulls) =
    let dirStr = maybe "" orderDirToString dir
        nullsStr = maybe "" nullsPosToString nulls
     in "\{toQueryPart expr} \{dirStr} \{nullsStr}"

namespace Grouping
  public export
  record SomeExpr (0 ty : Dir -> Type) where
    constructor MkSE
    expr : Expr ty a

  namespace FSSingle
    public export
    fromString : HasSignature n ty =>
                 (name : String) ->
                 {auto inSig : name `InSignature` signatureOf ty} ->
                 List (SomeExpr ty)
    fromString name = [MkSE $ col name]

  namespace FSMulti
    public export
    fromString : HasSignature n ty =>
                 (name : String) ->
                 {auto inSig : name `InSignature` signatureOf ty} ->
                 SomeExpr ty
    fromString name = MkSE $ col name

  export
  toQueryPart : List (SomeExpr ty) -> String
  toQueryPart = joinBy ", " . map (\se => toQueryPart se.expr)

public export
record Select (ty : Dir -> Type) (ret : Type) where
  constructor MkSelect
  {colCount : Nat}
  {auto isTableType : IsTupleLike colCount ty}
  selSrc : String
  columns : Columns ty ret
  whereClause : Expr ty Bool
  groupBy : List (SomeExpr ty)
  orderBy : Maybe (Order ty)

data DFrom : Type where
public export
from : Dummy DFrom
from = MkDF

namespace SelectTable
  export
  select : Dummy DFrom ->
           (ty : Dir -> Type) ->
           {n : _} ->
           IsTupleLike n ty =>
           IsSelectSource ty =>
           (Select ty (ty Read) -> Select ty ret) ->
           Select ty ret
  select _ ty f = f (MkSelect (selectSourceOf ty) CAll (1 == 1) [] Nothing)

namespace SelectJoin
  export
  select : Dummy DFrom ->
           {n : _} ->
           (st : SigTree n) ->
           IsValidTree st =>
           (Select (JoinTree st) (JoinTree st Read) -> Select (JoinTree st) ret) ->
           Select (JoinTree st) ret
  select _ st f = f (MkSelect (toFromPart st) CAll (1 == 1) [] Nothing)

namespace OptMaybe
  export
  opt : String -> (a -> String) -> Maybe a -> String
  opt _ _ Nothing = ""
  opt pref f (Just val) = pref ++ f val ++ " "

namespace OptList
  export
  opt : String -> (List a -> String) -> List a -> String
  opt _ _ [] = ""
  opt pref f ls = opt pref f (Just ls)

export
{ty, ret : _} -> Operation (Select ty ret) where
  returnType _ = List ret
  execute conn (MkSelect selSrc columns whereClause groupBy orderBy) = do
    let query = "SELECT \{joinBy ", " $ toColumnNames columns} " ++
                "FROM \{selSrc} " ++
                "WHERE \{toQueryPart whereClause} " ++
            opt "GROUP BY " toQueryPart groupBy ++
            opt "ORDER BY " toQueryPart orderBy
    result <- execParams' conn query []
    checkQueryStatus query result
    let rows = Data.Vect.Fin.tabulate {len = ntuples result} id
    case columns of
         CAll => do matches <- ensureMatches {numRows = ntuples result}
                    map toList $ for rows $ \row => fromTuple <$> extractFields result row _ matches
         CSome ixes => do matches <- ensureMatches {numRows = ntuples result}
                          map toList $ for rows $ \row => extractFields result row _ matches
