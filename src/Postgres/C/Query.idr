module Postgres.C.Query 

import Data.Fin
import Data.Vect

import Postgres.C.Connection
import Postgres.C.Utils

data ResTag : Type where

ResultHandle : Type
ResultHandle = Ptr ResTag

%foreign (libpq "exec")
ffi_exec : ConnHandle -> String -> PrimIO ResultHandle

%foreign (libpq "resultStatus")
ffi_resultStatus : ResultHandle -> PrimIO Int

%foreign (libpq "resultErrorMessage")
ffi_resultErrorMessage : ResultHandle -> PrimIO BorrowedString

%foreign (libpq "clear")
ffi_clear : ResultHandle -> PrimIO ()


export
data Result : (0 s : Type) -> Type where
  MkResult : (handle : ResultHandle) -> Result s

%name Result res

HandleWrapper ResultHandle Result where
  getHandle (MkResult h) = h


export
exec : HasIO io =>
       (conn : Conn s) ->
       (query : String) ->
       io (Result s)
exec conn query = MkResult <$> wrapFFI (`ffi_exec` query) conn


public export
data ResultStatus
  = EmptyQuery
  | CommandOk
  | TuplesOk
  | CopyOut
  | CopyIn
  | BadResponse
  | NonfatalError
  | FatalError
  | CopyBoth
  | SingleTuple
  | PipelineSync
  | PipelineAborted
  | Other Int

toResultStatus : Int -> ResultStatus
toResultStatus n = case integerToFin (cast n) (length knownStatuses) of
                        Nothing => Other n
                        Just idx => idx `index` knownStatuses
  where
    knownStatuses : Vect ? ResultStatus
    knownStatuses = [ EmptyQuery
                    , CommandOk
                    , TuplesOk
                    , CopyOut
                    , CopyIn
                    , BadResponse
                    , NonfatalError
                    , FatalError
                    , CopyBoth
                    , SingleTuple
                    , PipelineSync
                    , PipelineAborted
                    ]

export
resultStatus : HasIO io =>
               Result s ->
               io ResultStatus
resultStatus = map toResultStatus . wrapFFI ffi_resultStatus

export
resultErrorMessage : HasIO io =>
                     Result s ->
                     io String
resultErrorMessage = map asString . wrapFFI ffi_resultErrorMessage

export
clear : HasIO io =>
        Result s ->
        io ()
clear = wrapFFI ffi_clear
