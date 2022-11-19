module Postgres.C.Query 

import Data.Fin
import Data.Vect
import Derive.Prelude

import Postgres.C.Connection
import Postgres.C.Utils

%language ElabReflection

data ResTag : Type where

ResultHandle : Type
ResultHandle = Ptr ResTag

export
data Result : (0 s : Type) -> Type where
  MkResult : (handle : ResultHandle) -> Result s

%name Result res

HandleWrapper ResultHandle Result where
  getHandle (MkResult h) = h


%foreign (libpq "exec")
ffi_exec : ConnHandle -> String -> PrimIO ResultHandle

export
exec : HasIO io =>
       (conn : Conn s) ->
       (query : String) ->
       io (Result s)
exec conn query = MkResult <$> wrapFFI (`ffi_exec` query) conn


%foreign (libpq "resultStatus")
ffi_resultStatus : ResultHandle -> PrimIO Int

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

%runElab derive "ResultStatus" [Eq, Ord, Show]

export
isSuccessfulQuery : ResultStatus -> Bool
isSuccessfulQuery s = s == TuplesOk || s == SingleTuple

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


%foreign (libpq "resultErrorMessage")
ffi_resultErrorMessage : ResultHandle -> PrimIO BorrowedString

export
resultErrorMessage : HasIO io =>
                     Result s ->
                     io String
resultErrorMessage = map asString . wrapFFI ffi_resultErrorMessage


%foreign (libpq "clear")
ffi_clear : ResultHandle -> PrimIO ()

-- TODO use this as a finalizer
export
clear : HasIO io =>
        Result s ->
        io ()
clear = wrapFFI ffi_clear


%foreign (libpq "ntuples")
ffi_ntuples : ResultHandle -> PrimIO Int

export
ntuples : HasIO io =>
          Result s ->
          io Int
ntuples = wrapFFI ffi_ntuples


%foreign (libpq "nfields")
ffi_nfields : ResultHandle -> PrimIO Int

export
nfields : HasIO io =>
          Result s ->
          io Int
nfields = wrapFFI ffi_nfields


%foreign (libpq "ftype")
ffi_ftype : ResultHandle -> Int -> PrimIO Int

export
ftype : HasIO io =>
        Result s ->
        Int ->
        io Int
ftype r n = wrapFFI (`ffi_ftype` n) r