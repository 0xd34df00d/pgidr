module Postgres.Typed.MonadExec

import Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import Derive.Prelude

import Postgres.C
import public Postgres.C.Connection
import Postgres.Typed.PgType

%language ElabReflection
%default total

public export
data ExecError
  = ExpectationsMismatch String
  | QueryFailure ResultStatusCode String String
  | ValueParseError PgTyParseError
  | TODO
%runElab derive "ExecError" [Eq, Ord]

export
Show ExecError where
  show (ExpectationsMismatch str) = "expectations mismatch: \{str}"
  show (QueryFailure st str query) = "query `\{query}` failed, status code: \{show st}, error: \{str}"
  show (ValueParseError str) = "failed to parse value: " ++ str
  show TODO = "unimplemented (TODO)"

public export
data ResultStatus : Type where
  ResultSuccess : ResultStatus
  ResultError : (code : ResultStatusCode) -> (msg : String) -> ResultStatus

public export
interface MonadError ExecError m => MonadExec m where
  ||| Execute a query without any parameters.
  execQuery : Conn s -> String -> m (Result s)
  ||| Execute a query with a given vector of parameters.
  execQueryParams : Conn s -> String -> {n : _} -> Vect n String -> m (Result s)
  ||| Check query result status, returning the status and a potential error message.
  resultStatus : Result s -> m ResultStatus

export
runMonadExec : HasIO io => (forall m. MonadExec m => m res) -> io (Either ExecError res)
runMonadExec action = runEitherT {m = io} action
  where
  MonadExec (EitherT ExecError io) where
    execQuery = Postgres.C.exec
    execQueryParams = Postgres.C.execParams'
    resultStatus res = do
      status <- Postgres.C.resultStatus res
      if isSuccessfulQuery status
         then pure ResultSuccess
         else ResultError status <$> resultErrorMessage res

export
ensureQuerySuccess : MonadExec m =>
                     (query : String) ->
                     (res : Result s) ->
                     m ()
ensureQuerySuccess query res = resultStatus res >>= \case
  ResultSuccess => pure ()
  ResultError code msg => throwError $ QueryFailure code msg query
