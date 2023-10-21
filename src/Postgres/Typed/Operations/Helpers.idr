module Postgres.Typed.Operations.Helpers

import Decidable.Equality

import Postgres.C

import Postgres.Typed.Operations.Class
import Postgres.Typed.Tuple
import Postgres.Typed.Util

%default total
%prefix_record_projections off

public export
data HasName : SignatureElem -> String -> Type where
  MkHN : PgType type => (name : String) -> HasName (MkSE name type modifiers) name

public export
InSignature : String -> Signature n -> Type
InSignature name sig = Any (`HasName` name) sig

public export
namesToIxes : HasSignature n ty =>
              {k : _} ->
              {names : Vect k String} ->
              (alls : All (`InSignature` signatureOf ty) names) ->
              Vect k (Fin n)
namesToIxes [] = []
namesToIxes (inSig :: inSigs) = anyToFin inSig :: namesToIxes inSigs

public export
parseTextual' : MonadError ExecError m =>
                PgType ty =>
                (textual : String) ->
                m ty
parseTextual' textual = case fromTextual textual of
                             Left err => throwError $ ValueParseError err
                             Right res => pure res

public export
parseTextual : MonadError ExecError m =>
               (sigElem : SignatureElem) ->
               (textual : Maybe String) ->
               m (computeType' Read sigElem)
parseTextual (MkSE name ty mods) textual with (computeNullability mods Read)
  _ | NonNullable = maybe (unexpected "NULL value for \{name}") parseTextual' textual
  _ | Nullable = traverse parseTextual' textual

public export
record ResultMatches (res : Result s) (sig : Signature n) (rows : Nat) where
  constructor MkRM
  rowsMatch : ntuples res = rows
  colsMatch : nfields res = n

public export
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

public export
extractTextual : (res : Result s) ->
                 (row : RowI res) ->
                 (col : ColI res) ->
                 Maybe String
extractTextual res row col = if getisnull res row col
                                then Nothing
                                else Just $ getvalueTextual res row col

public export
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
