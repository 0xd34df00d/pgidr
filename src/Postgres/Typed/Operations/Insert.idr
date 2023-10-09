module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class

%default total
%prefix_record_projections off

namespace Returning
  public export
  data Columns : (0 ty : a) -> (0 ret : Type) -> Type where
    CNone : Columns ty ()
    CAll  : HasSignature n ty => Columns ty (ty Read)
    CSome : HasSignature n ty =>
            {k : _} ->
            (ixes : Vect k (Fin n)) ->
            Columns ty (Tuple (signatureOf ty `subColumns` ixes) Read)

  public export
  all : HasSignature n ty => Columns ty (ty Read)
  all = CAll

  public export
  data HasName : SignatureElem -> String -> Type where
    MkHN : PgType type => (name : String) -> HasName (MkSE name type modifiers) name

  public export
  InSignature : String -> Signature n -> Type
  InSignature name sig = Any (`HasName` name) sig

  public export
  anyToFin : {0 xs : Vect n _} -> Any p xs -> Fin n
  anyToFin (Here _) = FZ
  anyToFin (There later) = FS (anyToFin later)

  public export
  namesToIxes : HasSignature n ty =>
                {k : _} ->
                {names : Vect k String} ->
                (alls : All (`InSignature` signatureOf ty) names) ->
                Vect k (Fin n)
  namesToIxes [] = []
  namesToIxes (inSig :: inSigs) = anyToFin inSig :: namesToIxes inSigs

  public export
  ColsType : (ty : a) ->
             HasSignature n ty =>
             {k : _} ->
             {names : Vect k String} ->
             (alls : All (`InSignature` signatureOf ty) names) ->
             Type
  ColsType ty alls = Tuple (signatureOf ty `subColumns` namesToIxes alls) Read

  public export
  columns : HasSignature n ty =>
            {k : _} ->
            (names : Vect k String) ->
            {auto alls : All (`InSignature` signatureOf ty) names} ->
            Columns ty (ColsType ty alls)
  columns _ = CSome $ namesToIxes alls

  export
  toColumnNames : Columns ty ret -> Maybe (List String)
  toColumnNames CNone = Nothing
  toColumnNames CAll = Just $ toList $ allColumnNames (signatureOf ty)
  toColumnNames (CSome ixes) = Just $ toList $ columnNames (signatureOf ty) ixes

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

ensureMatches : MonadError ExecError m =>
                {n : _} ->
                (res : Result s) ->
                (sig : Signature n) ->
                m ()
ensureMatches res sig = do
  let natInterpolateLocal = MkInterpolation {a = Nat} show
  when (ntuples res /= 1) $ unexpected "\{ntuples res} tuples instead of one"
  when (nfields res /= n) $ unexpected "\{nfields res} columns instead of \{n}"
  -- TODO this could be the place to do extra checks
  -- for result column names/types/count
  -- if they are enabled

extractFields : MonadError ExecError m =>
                {n : _} ->
                (res : Result s) ->
                (sig : Signature n) ->
                m (Tuple sig Read)
extractFields res sig = do
  res `ensureMatches` sig
  let indices = tabulate $ \col => let col' = finToNat col in
                                    if getisnull res 0 col'
                                       then Nothing
                                       else Just $ getvalueTextual res 0 col'
  traverseProperty' parseTextual indices

export
{ty, ret : _} -> Operation (Insert ty ret) where
  returnType _ = ret
  execute conn (MkInsert _ _ val returning) = do
    let (_ ** cols) = mkInsertColumns val
        query = mkInsertQuery {ty} cols returning
        params = map (Just . .value) cols
    result <- execParams conn query params
    checkQueryStatus result
    case returning of
         CNone => pure ()
         CAll => fromRawTuple <$> extractFields result _
         CSome ixes => extractFields result _
