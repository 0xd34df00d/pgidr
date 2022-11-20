module Postgres.C.Connection

import Derive.Prelude

import Postgres.C.Utils

%default total

%language ElabReflection

data ConnTag : Type where

public export
ConnHandle : Type
ConnHandle = Ptr ConnTag

export
data Conn : (0 s : Type) -> Type where
  MkConn : (handle : ConnHandle) -> Conn s

%name Conn conn

export
HandleWrapper ConnHandle Conn where
  getHandle (MkConn h) = h


%foreign (libpq "connectdb")
ffi_connectdb : String -> PrimIO ConnHandle

%foreign (libpq "finish")
ffi_finish : ConnHandle -> PrimIO ()

export
withConnection : HasIO io =>
                 (connStr : String) ->
                 (f : {0 s : _} -> (c : Conn s) -> io a) ->
                 io a
withConnection connStr f = do
  conn <- primIO $ ffi_connectdb connStr
  res <- f {s = ()} $ MkConn conn
  primIO $ ffi_finish conn
  pure res


%foreign (libpq "status")
ffi_status : ConnHandle -> PrimIO Int

data ConnectionStatus
  = Ok
  | Bad
  | Other Int
%runElab derive "ConnectionStatus" [Eq, Ord, Show]

-- TODO eventually we'll need to query the actual values of these constants from C,
-- but this requires non-trivial changes to the build system to introduce our own
-- C helper library, which we're trying to avoid.
toConnectionStatus : Int -> ConnectionStatus
toConnectionStatus 0 = Ok
toConnectionStatus 1 = Bad
toConnectionStatus n = Other n

export
status : HasIO io => (c : Conn s) -> io ConnectionStatus
status = map toConnectionStatus . wrapFFI ffi_status


%foreign (libpq "errorMessage")
ffi_errorMessage : ConnHandle -> PrimIO BorrowedString

export
errorMessage : HasIO io => (c : Conn s) -> io String
errorMessage = map asString . wrapFFI ffi_errorMessage


%foreign (libpq "reset")
ffi_reset : ConnHandle -> PrimIO ()

export
reset : HasIO io => (c : Conn s) -> io ()
reset = wrapFFI ffi_reset


%foreign (libpq "serverVersion")
ffi_serverVersion : ConnHandle -> PrimIO Int

export
serverVersion : HasIO io => (c : Conn s) -> io Int
serverVersion = wrapFFI ffi_serverVersion
