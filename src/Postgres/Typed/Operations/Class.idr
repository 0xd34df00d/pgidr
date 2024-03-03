module Postgres.Typed.Operations.Class

import public Postgres.Typed.MonadExec

%default total

export
unexpected : MonadError ExecError m => String -> m a
unexpected = throwError . ExpectationsMismatch

public export
0
ExecuteFun : Type -> Type
ExecuteFun res = forall m. MonadExec m => m res

export
data Operation : (res : Type) -> Type where
  Pure : (val : res) -> Operation res
  Op : (opFun : ExecuteFun r1) -> (cont : r1 -> Operation r2) -> Operation r2

export
Functor Operation where
  map f (Pure val) = Pure (f val)
  map f (Op opFun cont) = Op opFun (map f . cont)

export
Applicative Operation where
  pure = Pure
  Pure fun <*> opVal = fun <$> opVal
  Op opFun cont <*> opVal = Op opFun ((<*> opVal) . cont)

export
Monad Operation where
  Pure val >>= f = f val
  Op opFun cont >>= f = Op opFun (\r => cont r >>= f)

export
singleOp : ExecuteFun res -> Operation res
singleOp = (`Op` Pure)

export
execute : Operation res -> MonadExec m => m res
execute (Pure val) = pure val
execute (Op opFun cont) = do
  r <- opFun
  execute $ cont r

export
execute' : HasIO io =>
           Conn s ->
           Operation res ->
           io (Either ExecError res)
execute' conn op = runMonadExec conn (execute op)
