module Postgres.Typed.Operations.Select

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple

import Postgres.Typed.Operations.Class
import public Postgres.Typed.Operations.Expression
import public Postgres.Typed.Operations.Helpers
import Postgres.Typed.Operations.Join

%default total
%prefix_record_projections off

namespace Output
  public export
  data Columns : (sig : Signature qk n) -> (ret : Type) -> Type where
    CAll    : {n : _} ->
              {sig : Signature _ n} ->
              Columns sig (List $ Tuple sig Read)
    CSome   : {k, n : _} ->
              {sig : Signature _ n} ->
              (ixes : Vect k (Fin n)) ->
              Columns sig (List $ Tuple (sig `subSignature` ixes) Read)

  export
  toColumnNames : Columns sig ret ->
                  List String
  toColumnNames CAll = map showName $ toList $ allColumnNames sig
  toColumnNames (CSome ixes) = map showName $ toList $ columnNames sig ixes

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
  record Order (sig : a) where
    constructor MkOrder
    orderExpr : Expr sig b
    direction : Maybe OrderDir
    nulls : Maybe NullsPos

  namespace FSU
    public export
    fromString : (name : String) ->
                 {sig : Signature Unqualified _} ->
                 {auto inSig : UName name `InSignature` sig} ->
                 Maybe (Order sig)
    fromString name = Just $ MkOrder (col $ UName name) Nothing Nothing

  namespace FSQ
    public export
    fromString : (name : String) ->
                 {sig : Signature Qualified _} ->
                 ValidQualifiedString name =>
                 {auto inSig : fromString name `InSignature` sig} ->
                 Maybe (Order sig)
    fromString name = Just $ MkOrder (col $ fromString name) Nothing Nothing

  export
  toQueryPart : Order _ ->
                String
  toQueryPart (MkOrder expr dir nulls) =
    let dirStr = maybe "" orderDirToString dir
        nullsStr = maybe "" nullsPosToString nulls
     in "\{toQueryPart expr} \{dirStr} \{nullsStr}"

namespace Grouping
  public export
  record SomeExpr (ty : a) where
    constructor MkSE
    expr : Expr ty r

  namespace FSSingle
    public export
    fromString : (name : Name qk) ->
                 {sig : Signature qk _} ->
                 {auto inSig : name `InSignature` sig} ->
                 List (SomeExpr sig)
    fromString name = [MkSE $ col name]

  namespace FSMulti
    public export
    fromString : (name : Name qk) ->
                 {sig : Signature qk _} ->
                 {auto inSig : name `InSignature` sig} ->
                 SomeExpr sig
    fromString name = MkSE $ col name

  export
  toQueryPart : List (SomeExpr sig) -> String
  toQueryPart = joinBy ", " . map (\se => toQueryPart se.expr)

data DFrom : Type where
public export 0
from : Dummy DFrom
from = MkDF

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

public export
record Select (sig : Signature qk n) (ret : Type) where
  constructor MkSelect
  selSrc : String
  columns : Columns sig ret
  where' : Expr sig Bool
  groupBy : List (SomeExpr sig)
  orderBy : Maybe (Order sig)

execSelect : Select sig ret ->
             ExecuteFun ret
execSelect (MkSelect selSrc columns whereClause groupBy orderBy) = do
  let query = "SELECT \{joinBy ", " $ toColumnNames columns} " ++
              "FROM \{selSrc} " ++
              "WHERE \{toQueryPart whereClause} " ++
          opt "GROUP BY " toQueryPart groupBy ++
          opt "ORDER BY " toQueryPart orderBy
  QueryResult result <- execQueryParams query []
  ensureQuerySuccess query result
  case columns of
       CAll => extractFieldsMany result _
       CSome ixes => extractFieldsMany result _

selectOp : Select sig ret ->
           Operation ret
selectOp = singleOp . execSelect

public export
0
SelectMod : Signature qk n -> Type -> Type
SelectMod sig ret = Select sig (List $ Tuple sig Read) ->
                    Select sig (List ret)

namespace SelectTable
  export
  select : (0 _ : Dummy DFrom) ->
           {n : _} ->
           (tbl : Table n) ->
           SelectMod tbl.signature ret ->
           Operation (List ret)
  select _ tbl f = selectOp $ f $ MkSelect tbl.name CAll (1 == 1) [] Nothing

namespace SelectJoin
  export
  select : (0 _ : Dummy DFrom) ->
           {n : _} ->
           (st : SigTree n) ->
           SelectMod (toSig st) ret ->
           Operation (List ret)
  select _ st f = selectOp $ f $ MkSelect (toFromPart st) CAll (1 == 1) [] Nothing
