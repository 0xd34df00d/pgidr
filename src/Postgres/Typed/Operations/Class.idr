module Postgres.Typed.Operations.Class

import Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import Derive.Prelude

import Postgres.C
import public Postgres.C.Connection
import Postgres.Typed.PgType

%default total
%language ElabReflection

public export
data ExecError
  = ExpectationsMismatch String
  | QueryFailure ResultStatus String String
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
MonadExec : (Type -> Type) -> Type
MonadExec m = (HasIO m, MonadError ExecError m)

export
unexpected : MonadError ExecError m => String -> m a
unexpected = throwError . ExpectationsMismatch

export
runMonadExec : HasIO io => (forall m. MonadExec m => m res) -> io (Either ExecError res)
runMonadExec action = runEitherT {m = io} action

public export
interface Operation opTy where
  returnType : opTy -> Type
  execute : MonadExec m =>
            Conn s ->
            (op : opTy) ->
            m (returnType op)

export
execute' : (Operation opTy, HasIO io) =>
           Conn s ->
           (op : opTy) ->
           io (Either ExecError (returnType op))
execute' conn op = runMonadExec (execute conn op)

export
checkQueryStatus : MonadExec m =>
                   (query : String) ->
                   (res : Result s) ->
                   m ()
checkQueryStatus query res = do
  status <- resultStatus res
  when (not $ isSuccessfulQuery status) $ do
    msg <- resultErrorMessage res
    throwError $ QueryFailure status msg query
