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
  public export
  typeAt : (0 ty : Dir -> Type) ->
           HasSignature n ty =>
           (idx : Fin n) ->
           Type
  typeAt ty idx = computeType' Read (idx `index` signatureOf ty)

  public export
  data Columns : (0 ty : Dir -> Type) -> (0 ret : Type) -> Type where
    CNone : Columns ty ()
    CAll  : HasSignature n ty => Columns ty (ty Read)
    COne  : HasSignature n ty =>
            (idx : Fin n) ->
            Columns ty (typeAt ty idx)
    CSome : HasSignature n ty =>
            {k : _} ->
            (idxes : Vect (S k) (Fin n)) ->
            Columns ty (subTuple ty idxes Read)

  public export
  all : HasSignature n ty => Columns ty (ty Read)
  all = CAll

  public export
  ColsType : (ty : Dir -> Type) ->
             HasSignature n ty =>
             {k : _} ->
             {names : Vect k String} ->
             (alls : All (`InSignature` signatureOf ty) names) ->
             Type
  ColsType ty alls = Tuple (signatureOf ty `subSignature` namesToIxes alls) Read

  public export
  columns : HasSignature n ty =>
            {k : _} ->
            (names : Vect (S k) String) ->
            {auto alls : All (`InSignature` signatureOf ty) names} ->
            Columns ty (ColsType ty alls)
  columns _ = CSome $ namesToIxes alls

  public export
  column : HasSignature n ty =>
           (name : String) ->
           {auto inSig : name `InSignature` signatureOf ty} ->
           Columns ty (computeType' Read (fromIsJust' inSig `index` signatureOf ty))
  column name = COne $ inSigToFin name (signatureOf ty) inSig

  export
  toColumnNames : Columns ty ret -> Maybe (List String)
  toColumnNames CNone = Nothing
  toColumnNames CAll = Just $ toList $ allColumnNames ty
  toColumnNames (COne idx) = Just [(idx `index` signatureOf ty).name]
  toColumnNames (CSome idxes) = Just $ toList $ columnNames ty idxes

record InsertColumn where
  constructor MkIC
  colName : String
  value : String

mkReturningClause : (returning : Columns ty ret) -> String
mkReturningClause = maybe "" (\cols => "RETURNING " ++ joinBy ", " cols) . toColumnNames

mkInsertQuery : {k : _} ->
                (HasSignature n ty, HasTableName ty) =>
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

mkInsertColumns : IsTupleLike n ty =>
                  (val : ty Write) ->
                  (k ** Vect k InsertColumn)
mkInsertColumns = catMaybes
                . forget
                . mapPropertyRelevant (\se => onSigValUniform (MkIC se.name . toTextual) se)
                . toTuple

public export
record Insert (ty : Dir -> Type) (ret : Type) where
  constructor MkInsert
  {fieldsCount : Nat}
  {auto tyIsTuple : IsTupleLike fieldsCount ty}
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
                  (sig : Signature n) ->
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

insertBase : Dummy DInto ->
             (ty : Dir -> Type) ->
             {n : _} ->
             (IsTupleLike n ty, HasTableName ty) =>
             (val : ty Write) ->
             Insert ty ()
insertBase _ _ val = MkInsert val CNone

insertOp : Insert ty ret -> Operation ret
insertOp = Op . execInsert

namespace InsertRecord
  export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           (IsTupleLike n ty, HasTableName ty) =>
           (val : ty Write) ->
           Operation ()
  insert d ty val = insertOp $ insertBase d ty val

  export
  insert' : Dummy DInto ->
            (ty : Dir -> Type) ->
            {n : _} ->
            (IsTupleLike n ty, HasTableName ty) =>
            (val : ty Write) ->
            (Insert ty () -> Insert ty ret) ->
            Operation ret
  insert' d ty val f = insertOp $ f (insertBase d ty val)

namespace InsertTuple
  export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           (IsTupleLike n ty, HasTableName ty) =>
           (val : Tuple (signatureOf ty) Write) ->
           Operation ()
  insert d ty = insertOp . insertBase d ty . fromTuple

  export
  insert' : Dummy DInto ->
            (ty : Dir -> Type) ->
            {n : _} ->
            (IsTupleLike n ty, HasTableName ty) =>
            (val : Tuple (signatureOf ty) Write) ->
            (Insert ty () -> Insert ty ret) ->
            Operation ret
  insert' d ty val f = insertOp $ f (insertBase d ty (fromTuple val))
