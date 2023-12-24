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

namespace ResultStatusCode
  public export
  data ResultStatusCode
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
%runElab derive "ResultStatusCode" [Eq, Ord, Show]

export
isSuccessfulQuery : ResultStatusCode -> Bool
isSuccessfulQuery s = s == CommandOk || s == TuplesOk || s == SingleTuple

-- TODO eventually we'll need to query the actual values of these constants from C,
-- but this requires non-trivial changes to the build system to introduce our own
-- C helper library, which we're trying to avoid.
toResultStatus : Int -> ResultStatusCode
toResultStatus n = case integerToFin (cast n) (length knownStatuses) of
                        Nothing => Other n
                        Just idx => idx `index` knownStatuses
  where
  knownStatuses : Vect ? ResultStatusCode
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
               io ResultStatusCode
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
          Nat
ntuples = cast . wrapFFIpure ffi_ntuples


%foreign (libpq "nfields")
ffi_nfields : ResultHandle -> Int

export
nfields : (res : Result s) ->
          Nat
nfields = cast . wrapFFIpure ffi_nfields


%foreign (libpq "fname")
ffi_fname : ResultHandle -> Int -> BorrowedString

export
fname : (res : Result s) ->
        (col : Nat) ->
        String
fname res col = asString $ wrapFFIpure (`ffi_fname` cast col) res


%foreign (libpq "ftype")
ffi_ftype : ResultHandle -> Int -> Int

export
ftype : (res : Result s) ->
        (col : Nat) ->
        Int
ftype res col = wrapFFIpure (`ffi_ftype` cast col) res

%foreign (libpq "fmod")
ffi_fmod : ResultHandle -> Int -> Int

export
fmod : (res : Result s) ->
       (col : Nat) ->
       Int
fmod res col = wrapFFIpure (`ffi_fmod` cast col) res

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
          (col : Nat) ->
          ColumnFormat
fformat res col = toColumnFormat $ wrapFFIpure (`ffi_fformat` cast col) res


%foreign (libpq "getisnull")
ffi_getisnull : ResultHandle -> Int -> Int -> Int

export
getisnull : (res : Result s) ->
            (row, col : Nat) ->
            Bool
getisnull res row col = (== 1) $ wrapFFIpure (\h => ffi_getisnull h (cast row) (cast col)) res

%foreign (libpq "getlength")
ffi_getlength : ResultHandle -> Int -> Int -> Int

export
getlength : (res : Result s) ->
            (row, col : Nat) ->
            Int
getlength res row col = wrapFFIpure (\h => ffi_getlength h (cast row) (cast col)) res

%foreign (libpq "getvalue")
ffi_getvalue : ResultHandle -> Int -> Int -> Ptr Bits8

export
getvalue : (res : Result s) ->
           (row, col : Nat) ->
           Ptr Bits8
getvalue res row col = wrapFFIpure (\h => ffi_getvalue h (cast row) (cast col)) res

export
getvalueTextual : (res : Result s) ->
                  (row, col : Nat) ->
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

export
execParams' : HasIO io =>
              (conn : Conn s) ->
              (command : String) ->
              {n : _} ->
              (params : Vect n String) ->
              io (Result s)
execParams' conn command = execParams conn command . map Just


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

public export
ColI : Result s -> Type
ColI res = Fin (nfields res)

public export
RowI : Result s -> Type
RowI res = Fin (ntuples res)

namespace Bounded
  public export
  BoundedC : Type -> Type
  BoundedC a = forall s.
               (res : Result s) ->
               (col : ColI res) ->
               a

  wrapC : (forall s. Result s -> Nat -> a) ->
          BoundedC a
  wrapC f res = f res . finToNat

  public export
  BoundedRC : Type -> Type
  BoundedRC a = forall s.
                (res : Result s) ->
                (row : RowI res) ->
                (col : ColI res) ->
                a

  wrapRC : (forall s. Result s -> Nat -> Nat -> a) ->
           BoundedRC a
  wrapRC f res row col = f res (finToNat row) (finToNat col)

  export
  fname : BoundedC String
  fname = wrapC fname

  export
  ftype : BoundedC Int
  ftype = wrapC ftype

  export
  fmod : BoundedC Int
  fmod = wrapC fmod

  export
  fformat : BoundedC ColumnFormat
  fformat = wrapC fformat

  export
  getisnull : BoundedRC Bool
  getisnull = wrapRC getisnull

  export
  getlength : BoundedRC Int
  getlength = wrapRC getlength

  export
  getvalue : BoundedRC (Ptr Bits8)
  getvalue = wrapRC getvalue

  export
  getvalueTextual : BoundedRC String
  getvalueTextual = wrapRC getvalueTextual

  export
  onColumns : (f : BoundedC a) ->
              (res : Result s) ->
              Vect (nfields res) a
  onColumns f res = tabulate (f res)
