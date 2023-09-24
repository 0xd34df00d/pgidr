module Postgres.Typed.Util

import Postgres.C

%default total

export
checkStatus : HasIO io =>
              Result s ->
              io (Either String ())
checkStatus res = resultStatus res >>=
  \case CommandOk => pure $ pure ()
        _ => Left <$> resultErrorMessage res
