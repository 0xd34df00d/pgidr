module Postgres.Typed.Operations.Class

import Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import Derive.Prelude

import Postgres.C

%default total
%language ElabReflection

public export
data ExecError
  = ExpectationsMismatch String
  | QueryFailure ResultStatus String
%runElab derive "ExecError" [Eq, Ord, Show]

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
                   Result s ->
                   m ()
checkQueryStatus res = do
  status <- resultStatus res
  when (not $ isSuccessfulQuery status) $ do
    msg <- resultErrorMessage res
    throwError $ QueryFailure status msg
