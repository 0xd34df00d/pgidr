module Postgres.Typed.Operations.Class

import Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import Derive.Prelude

import Postgres.C
import public Postgres.C.Connection
import Postgres.Typed.PgType

%language ElabReflection
%default total
%prefix_record_projections off

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

public export 0
MonadExec : (Type -> Type) -> Type
MonadExec m = (HasIO m, MonadError ExecError m)

export
unexpected : MonadError ExecError m => String -> m a
unexpected = throwError . ExpectationsMismatch

export
runMonadExec : HasIO io => (forall m. MonadExec m => m res) -> io (Either ExecError res)
runMonadExec action = runEitherT {m = io} action

public export 0
ExecuteFun : Type -> Type
ExecuteFun res = forall m, s. MonadExec m => Conn s -> m res

export
data Operation : (res : Type) -> Type where
  Pure : (val : res) -> Operation res
  Op : (opFun : ExecuteFun r1) -> (cont : r1 -> Operation r2) -> Operation r2

export
singleOp : ExecuteFun res -> Operation res
singleOp = (`Op` Pure)

export
execute : MonadExec m => Conn s -> Operation res -> m res
execute conn (Pure val) = pure val
execute conn (Op opFun cont) = do
  r <- opFun conn
  execute conn $ cont r

export
execute' : HasIO io =>
           Conn s ->
           Operation res ->
           io (Either ExecError res)
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
