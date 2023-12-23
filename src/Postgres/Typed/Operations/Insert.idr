module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect

import Data.Vect.Quantifiers.Extra

import Postgres.C

import public Postgres.Typed.Tuple

import Postgres.Typed.Operations.Class
import Postgres.Typed.Operations.Helpers

%default total
%prefix_record_projections off

namespace Returning
  public export 0
  typeAt : (0 ty : Dir -> Type) ->
           HasSignature Unqualified n ty =>
           (idx : Fin n) ->
           Type
  typeAt ty idx = computeType' Read (idx `index` signatureOf ty)

  public export
  data Columns : (ty : Dir -> Type) -> (ret : Type) -> Type where
    CNone : Columns ty ()
    CAll  : HasSignature Unqualified n ty => Columns ty (ty Read)
    COne  : HasSignature Unqualified n ty =>
            (idx : Fin n) ->
            Columns ty (typeAt ty idx)
    CSome : HasSignature Unqualified n ty =>
            {k : _} ->
            (idxes : Vect (S k) (Fin n)) ->
            Columns ty (subTuple ty idxes Read)

  public export
  all : HasSignature Unqualified n ty => Columns ty (ty Read)
  all = CAll

  public export
  ColsType : (ty : Dir -> Type) ->
             HasSignature Unqualified n ty =>
             {k : _} ->
             {names : Vect k (Name Unqualified)} ->
             (alls : All (`InSignature` signatureOf ty) names) ->
             Type
  ColsType ty alls = Tuple (signatureOf ty `subSignature` namesToIxes alls) Read

  public export
  columns : HasSignature Unqualified n ty =>
            {k : _} ->
            (names : Vect (S k) (Name Unqualified)) ->
            {auto alls : All (`InSignature` signatureOf ty) names} ->
            Columns ty (ColsType ty alls)
  columns _ = CSome $ namesToIxes alls

  public export
  column : HasSignature Unqualified n ty =>
           (name : Name Unqualified) ->
           {auto inSig : name `InSignature` signatureOf ty} ->
           Columns ty (computeType' Read (inSigToFin inSig `index` signatureOf ty))
  column _ = COne $ inSigToFin inSig

  export
  toColumnNames : Columns ty ret -> Maybe (List String)
  toColumnNames CNone = Nothing
  toColumnNames CAll = Just $ map (.uname) $ toList $ allColumnNames ty
  toColumnNames (COne idx) = Just [(idx `index` signatureOf ty).name.uname]
  toColumnNames (CSome idxes) = Just $ map (.uname) $ toList $ columnNames ty idxes

record InsertColumn where
  constructor MkIC
  colName : String
  value : String

mkReturningClause : (returning : Columns ty ret) -> String
mkReturningClause = maybe "" (\cols => "RETURNING " ++ joinBy ", " cols) . toColumnNames

mkInsertQuery : {k : _} ->
                (HasSignature Unqualified n ty, HasTableName ty) =>
                (cols : Vect k InsertColumn) ->
                (returning : Columns ty ret) ->
                String
mkInsertQuery cols returning =
  let namesStr = joinBy ", " $ toList $ .colName <$> cols
      placeholders = joinBy ", "
                   $ toList
                   $ tabulate {len = k} (\i => "$" ++ show (finToNat i + 1))
      returningClause = mkReturningClause returning
   in "INSERT INTO \{tableNameOf ty} (\{namesStr}) VALUES (\{placeholders}) \{returningClause}"

mkInsertColumns : IsTupleLike Unqualified n ty =>
                  (val : ty Write) ->
                  (k ** Vect k InsertColumn)
mkInsertColumns = catMaybes
                . forget
                . mapPropertyRelevant (\se => onSigValUniform (MkIC se.name.uname . toTextual) se)
                . toTuple

public export
record Insert (ty : Dir -> Type) (ret : Type) where
  constructor MkInsert
  {fieldsCount : Nat}
  {auto tyIsTuple : IsTupleLike Unqualified fieldsCount ty}
  {auto tyHasTable : HasTableName ty}
  value : ty Write
  returning : Columns ty ret

data DInto : Type where
public export
into : Dummy DInto
into = MkDF

extractFirstRow : MonadError ExecError m =>
                  {n : _} ->
                  (res : Result s) ->
                  (sig : Signature Unqualified n) ->
                  (0 matches : ResultMatches res sig 1) ->
                  m (Tuple sig Read)
extractFirstRow res sig matches = extractFields res (rewrite matches.rowsMatch in 0) sig matches

infixl 1 =<<|
(=<<|) : Monad m => ((0 _ : a) -> m b) -> m a -> m b
f =<<| act = act >>= \r => f r

execInsert : Insert ty ret -> ExecuteFun ret
execInsert (MkInsert val returning) conn = do
  let (_ ** cols) = mkInsertColumns val
      query = mkInsertQuery {ty} cols returning
      params = map (.value) cols
  result <- execParams' conn query params
  checkQueryStatus query result
  case returning of
       CNone => pure ()
       CAll => fromTuple <$> (extractFirstRow result _ =<<| ensureMatches)
       COne idx => head <$> (extractFirstRow result (subSignature _ [idx]) =<<| ensureMatches)
       CSome idxes => extractFirstRow result _ =<<| ensureMatches

insertBase : (0 ty : Dir -> Type) ->
             {n : _} ->
             (IsTupleLike Unqualified n ty, HasTableName ty) =>
             (val : ty Write) ->
             Insert ty ()
insertBase _ val = MkInsert val CNone

insertOp : Insert ty ret -> Operation ret
insertOp = Op . execInsert

namespace InsertRecord
  export
  insert : (0 _ : Dummy DInto) ->
           (0 ty : Dir -> Type) ->
           {n : _} ->
           (IsTupleLike Unqualified n ty, HasTableName ty) =>
           (val : ty Write) ->
           Operation ()
  insert _ ty val = insertOp $ insertBase ty val

  export
  insert' : (0 _ : Dummy DInto) ->
            (0 ty : Dir -> Type) ->
            {n : _} ->
            (IsTupleLike Unqualified n ty, HasTableName ty) =>
            (val : ty Write) ->
            (Insert ty () -> Insert ty ret) ->
            Operation ret
  insert' _ ty val f = insertOp $ f (insertBase ty val)

namespace InsertTuple
  export
  insert : (0 _ : Dummy DInto) ->
           (0 ty : Dir -> Type) ->
           {n : _} ->
           (IsTupleLike Unqualified n ty, HasTableName ty) =>
           (val : Tuple (signatureOf ty) Write) ->
           Operation ()
  insert _ ty = insertOp . insertBase ty . fromTuple

  export
  insert' : (0 _ : Dummy DInto) ->
            (0 ty : Dir -> Type) ->
            {n : _} ->
            (IsTupleLike Unqualified n ty, HasTableName ty) =>
            (val : Tuple (signatureOf ty) Write) ->
            (Insert ty () -> Insert ty ret) ->
            Operation ret
  insert' _ ty val f = insertOp $ f (insertBase ty (fromTuple val))
