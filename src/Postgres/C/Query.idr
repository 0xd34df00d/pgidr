module Postgres.C.Query

import Data.Buffer
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

addResultFinalizer : HasIO io => UnmanagedResultHandle -> io (Result s)
addResultFinalizer uhandle = do
  handle <- onCollect uhandle $ primIO . ffi_clear
  pure $ MkResult handle

wrapFFIResult : (HasIO io) =>
                (ConnHandle -> PrimIO UnmanagedResultHandle) ->
                (c : Conn s) ->
                io (Result s)
wrapFFIResult ffi conn = wrapFFI ffi conn >>= addResultFinalizer

export
exec : HasIO io =>
       (conn : Conn s) ->
       (query : String) ->
       io (Result s)
exec conn query = wrapFFIResult (`ffi_exec` query) conn


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
ffi_ntuples : ResultHandle -> Int

export
ntuples : (res : Result s) ->
          Int
ntuples = wrapFFIpure ffi_ntuples


%foreign (libpq "nfields")
ffi_nfields : ResultHandle -> Int

export
nfields : (res : Result s) ->
          Int
nfields = wrapFFIpure ffi_nfields


%foreign (libpq "fname")
ffi_fname : ResultHandle -> Int -> BorrowedString

export
fname : (res : Result s) ->
        (column : Int) ->
        String
fname res col = asString $ wrapFFIpure (`ffi_fname` col) res


%foreign (libpq "ftype")
ffi_ftype : ResultHandle -> Int -> Int

export
ftype : (res : Result s) ->
        (col : Int) ->
        Int
ftype r n = wrapFFIpure (`ffi_ftype` n) r

%foreign (libpq "fmod")
ffi_fmod : ResultHandle -> Int -> Int

export
fmod : (res : Result s) ->
       (col : Int) ->
       Int
fmod r n = wrapFFIpure (`ffi_fmod` n) r

%foreign (libpq "fformat")
ffi_fformat : ResultHandle -> Int -> Int

namespace ColumnFormat
  public export
  data ColumnFormat
    = Textual
    | Binary
    | Other Int
%runElab derive "ColumnFormat" [Eq, Ord, Show]

toColumnFormat : Int -> ColumnFormat
toColumnFormat 0 = Textual
toColumnFormat 1 = Binary
toColumnFormat n = Other n

Cast ColumnFormat Int where
  cast Textual = 0
  cast Binary = 1
  cast (Other n) = n

export
fformat : (res : Result s) ->
          (col : Int) ->
          ColumnFormat
fformat res col = toColumnFormat $ wrapFFIpure (`ffi_fformat` col) res


%foreign (libpq "getisnull")
ffi_getisnull : ResultHandle -> Int -> Int -> Int

export
getisnull : (res : Result s) ->
            (row, col : Int) ->
            Bool
getisnull res row col = (== 1) $ wrapFFIpure (\h => ffi_getisnull h row col) res

%foreign (libpq "getlength")
ffi_getlength : ResultHandle -> Int -> Int -> Int

export
getlength : (res : Result s) ->
            (row, col : Int) ->
            Int
getlength res row col = wrapFFIpure (\h => ffi_getlength h row col) res

%foreign (libpq "getvalue")
ffi_getvalue : ResultHandle -> Int -> Int -> Ptr Bits8

export
getvalue : (res : Result s) ->
           (row, col : Int) ->
           Ptr Bits8
getvalue res row col = wrapFFIpure (\h => ffi_getvalue h row col) res

export
getvalueTextual : (res : Result s) ->
                  (row, col : Int) ->
                  String
getvalueTextual res row col = convert $ getvalue res row col
  where
    convert : Ptr Bits8 -> String
    convert = asString . prim__castPtr . prim__forgetPtr

nullptr : Ptr t
nullptr = prim__castPtr prim__getNullAnyPtr

%foreign (libpq "execParams")
ffi_execParams : (conn : ConnHandle) ->
                 (command : String) ->
                 (nParams : Int) ->
                 (paramTypes : Ptr Int) ->
                 (paramValues : Buffer) ->
                 (paramLengths : Ptr Int) ->
                 (paramFormats : Ptr Int) ->
                 (resultFormat : Int) ->
                 PrimIO UnmanagedResultHandle

ffi_execParams' : (conn : ConnHandle) ->
                  (command : String) ->
                  (nParams : Int) ->
                  (paramValues : Buffer) ->
                  (resultFormat : Int) ->
                  PrimIO UnmanagedResultHandle
ffi_execParams' conn command nParams paramValues resultFormat =
  ffi_execParams conn command nParams nullptr paramValues nullptr nullptr resultFormat

nullGcPtr : HasIO io => io (GCPtr t)
nullGcPtr = onCollect nullptr (const $ pure ())

withStringArray : HasIO io =>
                  {n : _} ->
                  (params : Vect n (Maybe String)) ->
                  (cont : Buffer -> io (Result s)) ->
                  io (Result s)
withStringArray params cont = toStringArray params >>= maybe (MkResult <$> nullGcPtr) cont

export
execParams : HasIO io =>
             (conn : Conn s) ->
             (command : String) ->
             {n : _} ->
             (params : Vect n (Maybe String)) ->
             io (Result s)
execParams conn command params =
  withStringArray params $ \paramsArray =>
    wrapFFIResult (\conn' => ffi_execParams' conn' command (cast n) paramsArray (cast Textual)) conn


%foreign (libpq "prepare")
ffi_prepare : (conn : ConnHandle) ->
              (stmtName : String) ->
              (query : String) ->
              (nParams : Int) ->
              (paramTypes : Ptr Int) ->
              PrimIO UnmanagedResultHandle

export
prepare : HasIO io =>
          (conn : Conn s) ->
          (stmtName : String) ->
          (query : String) ->
          io (Result s)
prepare conn stmtName query = wrapFFIResult (\conn' => ffi_prepare conn' stmtName query 0 nullptr) conn

%foreign (libpq "execPrepared")
ffi_execPrepared : (conn : ConnHandle) ->
                   (stmtName : String) ->
                   (nParams : Int) ->
                   (paramValues : Buffer) ->
                   (paramLengths : Ptr Int) ->
                   (paramFormats : Ptr Int) ->
                   (resultFormat : Int) ->
                   PrimIO UnmanagedResultHandle

export
execPrepared : HasIO io =>
               (conn : Conn s) ->
               (stmtName : String) ->
               {n : _} ->
               (params : Vect n (Maybe String)) ->
               io (Result s)
execPrepared conn stmtName params =
  withStringArray params $ \paramsArray =>
    wrapFFIResult (\conn' => ffi_execPrepared conn' stmtName (cast n) paramsArray nullptr nullptr (cast Textual)) conn
