module Postgres.Typed.Operations.Class

import Postgres.C

%default total

public export
interface Operation opTy where
  returnType : opTy -> Type
  execute : HasIO io =>
            Conn s ->
            (op : opTy) ->
            io (Either String (returnType op))
