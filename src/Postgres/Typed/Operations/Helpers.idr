module Postgres.Typed.Operations.Helpers

import Decidable.Equality

import Data.Vect.Quantifiers.Extra

import Postgres.C

import Postgres.Typed.Operations.Class
import Postgres.Typed.Tuple

public export
record Dummy (tag : Type) where
  constructor MkDF


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
               {qk : _} ->
               (sigElem : SignatureElem qk) ->
               (textual : Maybe String) ->
               m (computeType' Read sigElem)
parseTextual (MkSE name ty mods) textual with (computeNullability mods Read)
  _ | NonNullable = maybe (unexpected "NULL value for \{showName name}") parseTextual' textual
  _ | Nullable = traverse parseTextual' textual

public export
record ResultMatches (res : Result s) (sig : Signature qk n) (numRows : Nat) where
  constructor MkRM
  rowsMatch : ntuples res = numRows
  colsMatch : nfields res = n

public export
ensureMatches : MonadError ExecError m =>
                {n, numRows : _} ->
                {res : Result s} ->
                {0 sig : Signature qk n} ->
                m (ResultMatches res sig numRows)
ensureMatches = do
  let natInterpolateLocal = MkInterpolation {a = Nat} show
  Yes rowsMatch <- pure $ ntuples res `decEq` numRows
    | No _ => unexpected "\{ntuples res} tuples instead of one"
  Yes colsMatch <- pure $ nfields res `decEq` n
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
                {qk, n : _} ->
                (res : Result s) ->
                (row : RowI res) ->
                (sig : Signature qk n) ->
                (0 matches : ResultMatches res sig numRows) ->
                m (Tuple sig Read)
extractFields res row sig (MkRM _ Refl) = do
  let indices = tabulate (extractTextual res row)
  traversePropertyRelevant parseTextual indices
