module Postgres.C.Query 

import Data.Fin
import Data.Vect
import Derive.Prelude

import Postgres.C.Connection
import Postgres.C.Utils

%default total

%language ElabReflection

data ResTag : Type where

UnmanagedResultHandle : Type
UnmanagedResultHandle = Ptr ResTag

ResultHandle : Type
ResultHandle = GCPtr ResTag

export
data Result : (0 s : Type) -> Type where
  MkResult : (handle : ResultHandle) -> Result s

%name Result res

HandleWrapper ResultHandle Result where
  getHandle (MkResult h) = h

%foreign (libpq "clear")
ffi_clear : UnmanagedResultHandle -> PrimIO ()


%foreign (libpq "exec")
ffi_exec : ConnHandle -> String -> PrimIO UnmanagedResultHandle

export
exec : HasIO io =>
       (conn : Conn s) ->
       (query : String) ->
       io (Result s)
exec conn query = do
  uhandle <- wrapFFI (`ffi_exec` query) conn
  handle <- onCollect uhandle $ primIO . ffi_clear
  pure $ MkResult handle


%foreign (libpq "resultStatus")
ffi_resultStatus : ResultHandle -> PrimIO Int

namespace ResultStatus
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

-- TODO eventually we'll need to query the actual values of these constants from C,
-- but this requires non-trivial changes to the build system to introduce our own
-- C helper library, which we're trying to avoid.
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
               (res : Result s) ->
               io ResultStatus
resultStatus = map toResultStatus . wrapFFI ffi_resultStatus


%foreign (libpq "resultErrorMessage")
ffi_resultErrorMessage : ResultHandle -> PrimIO BorrowedString

export
resultErrorMessage : HasIO io =>
                     (res : Result s) ->
                     io String
resultErrorMessage = map asString . wrapFFI ffi_resultErrorMessage


%foreign (libpq "ntuples")
ffi_ntuples : ResultHandle -> PrimIO Int

export
ntuples : HasIO io =>
          (res : Result s) ->
          io Int
ntuples = wrapFFI ffi_ntuples


%foreign (libpq "nfields")
ffi_nfields : ResultHandle -> PrimIO Int

export
nfields : HasIO io =>
          (res : Result s) ->
          io Int
nfields = wrapFFI ffi_nfields


%foreign (libpq "ftype")
ffi_ftype : ResultHandle -> Int -> PrimIO Int

export
ftype : HasIO io =>
        (res : Result s) ->
        (col : Int) ->
        io Int
ftype r n = wrapFFI (`ffi_ftype` n) r

%foreign (libpq "fmod")
ffi_fmod : ResultHandle -> Int -> PrimIO Int

export
fmod : HasIO io =>
       (res : Result s) ->
       (col : Int) ->
       io Int
fmod r n = wrapFFI (`ffi_fmod` n) r

%foreign (libpq "fformat")
ffi_fformat : ResultHandle -> Int -> PrimIO Int

namespace ColumnFormat
  public export
  data ColumnFormat
    = Textual
    | Binary
    | Other Int
%runElab derive "ColumnFormat" [Eq, Ord, Show]

-- TODO eventually we'll need to query the actual values of these constants from C,
-- but this requires non-trivial changes to the build system to introduce our own
-- C helper library, which we're trying to avoid.
toColumnFormat : Int -> ColumnFormat
toColumnFormat 0 = Textual
toColumnFormat 1 = Binary
toColumnFormat n = Other n

export
fformat : HasIO io =>
          (res : Result s) ->
          (col : Int) ->
          io ColumnFormat
fformat res col = toColumnFormat <$> wrapFFI (`ffi_fformat` col) res


%foreign (libpq "getisnull")
ffi_getisnull : ResultHandle -> Int -> Int -> PrimIO Int

export
getisnull : HasIO io =>
            (res : Result s) ->
            (row, col : Int) ->
            io Bool
getisnull res row col = (== 1) <$> wrapFFI (\h => ffi_getisnull h row col) res

%foreign (libpq "getlength")
ffi_getlength : ResultHandle -> Int -> Int -> PrimIO Int

export
getlength : HasIO io =>
            (res : Result s) ->
            (row, col : Int) ->
            io Int
getlength res row col = wrapFFI (\h => ffi_getlength h row col) res

%foreign (libpq "getvalue")
ffi_getvalue : ResultHandle -> Int -> Int -> PrimIO (Ptr Bits8)

export
getvalue : HasIO io =>
           (res : Result s) ->
           (row, col : Int) ->
           io (Ptr Bits8)
getvalue res row col = wrapFFI (\h => ffi_getvalue h row col) res

export
getvalueTextual : HasIO io =>
                  (res : Result s) ->
                  (row, col : Int) ->
                  io String
getvalueTextual res row col = convert <$> getvalue res row col
  where
    convert : Ptr Bits8 -> String
    convert = asString . prim__castPtr . prim__forgetPtr
