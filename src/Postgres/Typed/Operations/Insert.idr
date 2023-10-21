module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect
import Decidable.Equality

import Postgres.C

import public Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class
import public Postgres.Typed.Operations.Helpers

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
  ColsType ty alls = Tuple (signatureOf ty `subColumns` namesToIxes alls) Read

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
           Columns ty (computeType' Read (anyToFin inSig `index` signatureOf ty))
  column _ = COne $ anyToFin inSig

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
mkReturningClause = maybe "" (\cols => "RETURNING " ++ joinBy "," cols) . toColumnNames

mkInsertQuery : {k : _} ->
                HasSignature n ty =>
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

mkInsertColumns : IsRecordType n ty =>
                  (val : ty Write) ->
                  (k ** Vect k InsertColumn)
mkInsertColumns = catMaybes
                . forget
                . mapProperty' (\se => onSigValUniform (MkIC se.name . toTextual) se)
                . columns
                . toTuple

public export
record Insert (ty : Dir -> Type) (ret : Type) where
  constructor MkInsert
  fieldsCount : Nat
  tyIsRecord : IsRecordType fieldsCount ty    -- TODO make auto implicit when Idris2#3083 is fixed
  value : ty Write
  returning : Columns ty ret

data DInto : Type where
public export
into : Dummy DInto
into = MkDF

namespace InsertRecord
  public export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           IsRecordType n ty =>
           (val : ty Write) ->
           Insert ty ()
  insert _ _ val = MkInsert _ %search val CNone

  public export
  insert' : Dummy DInto ->
            (ty : Dir -> Type) ->
            {n : _} ->
            IsRecordType n ty =>
            (val : ty Write) ->
            (Insert ty () -> Insert ty ret) ->
            Insert ty ret
  insert' d ty val f = f (insert d ty val)

namespace InsertTuple
  public export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           IsRecordType n ty =>
           (val : Tuple (signatureOf ty) Write) ->
           Insert ty ()
  insert d ty = insert d ty . fromRawTuple

  public export
  insert' : Dummy DInto ->
            (ty : Dir -> Type) ->
            {n : _} ->
            IsRecordType n ty =>
            (val : Tuple (signatureOf ty) Write) ->
            (Insert ty () -> Insert ty ret) ->
            Insert ty ret
  insert' d ty val f = insert' d ty (fromRawTuple val) f

parseTextual' : MonadError ExecError m =>
                PgType ty =>
                (textual : String) ->
                m ty
parseTextual' textual = case fromTextual textual of
                             Left err => throwError $ ValueParseError err
                             Right res => pure res

parseTextual : MonadError ExecError m =>
               (sigElem : SignatureElem) ->
               (textual : Maybe String) ->
               m (computeType' Read sigElem)
parseTextual (MkSE name ty mods) textual with (computeNullability mods Read)
  _ | NonNullable = maybe (unexpected "NULL value for \{name}") parseTextual' textual
  _ | Nullable = traverse parseTextual' textual

record ResultMatches (res : Result s) (sig : Signature n) (rows : Nat) where
  constructor MkRM
  rowsMatch : ntuples res = rows
  colsMatch : nfields res = n

ensureMatches : MonadError ExecError m =>
                {n, rows : _} ->
                {res : Result s} ->
                {0 sig : Signature n} ->
                m (ResultMatches res sig rows)
ensureMatches = do
  let natInterpolateLocal = MkInterpolation {a = Nat} show
  Yes rowsMatch <- pure $ ntuples res `decEq` rows
    | No _ => unexpected "\{ntuples res} tuples instead of one"
  Yes colsMatch <- pure $ decEq (nfields res) n
    | No _ => unexpected "\{nfields res} columns instead of \{n}"
  pure $ MkRM rowsMatch colsMatch
  -- TODO this could be the place to do extra checks
  -- for result column names/types/count
  -- if they are enabled

extractTextual : (res : Result s) ->
                 (row : RowI res) ->
                 (col : ColI res) ->
                 Maybe String
extractTextual res row col = if getisnull res row col
                                then Nothing
                                else Just $ getvalueTextual res row col

extractFields : MonadError ExecError m =>
                {n : _} ->
                (res : Result s) ->
                (row : RowI res) ->
                (sig : Signature n) ->
                (0 matches : ResultMatches res sig rows) ->
                m (Tuple sig Read)
extractFields res row sig (MkRM _ Refl) = do
  let indices = tabulate (extractTextual res row)
  traversePropertyRelevant parseTextual indices

extractFirstRow : MonadError ExecError m =>
                  {n : _} ->
                  (res : Result s) ->
                  (sig : Signature n) ->
                  (0 matches : ResultMatches res sig 1) ->
                  m (Tuple sig Read)
extractFirstRow res sig matches = extractFields res (rewrite matches.rowsMatch in 0) sig matches

export
{ty, ret : _} -> Operation (Insert ty ret) where
  returnType _ = ret
  execute conn (MkInsert _ _ val returning) = do
    let (_ ** cols) = mkInsertColumns val
        query = mkInsertQuery {ty} cols returning
        params = map (.value) cols
    result <- execParams' conn query params
    checkQueryStatus result
    case returning of
         CNone => pure ()
         CAll => do matches <- ensureMatches
                    fromRawTuple <$> extractFirstRow result _ matches
         COne idx => do matches <- ensureMatches
                        [val] <- extractFirstRow result (subColumns _ [idx]) matches
                        pure val
         CSome idxes => do matches <- ensureMatches
                           extractFirstRow result _ matches
