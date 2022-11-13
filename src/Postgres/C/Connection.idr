module Postgres.C.Connection

import Postgres.C.Utils

data ConnTag : Type where

public export
ConnHandle : Type
ConnHandle = Ptr ConnTag

%foreign (libpq "connectdb")
ffi_connectdb : String -> PrimIO ConnHandle

%foreign (libpq "finish")
ffi_finish : ConnHandle -> PrimIO ()

%foreign (libpq "reset")
ffi_reset : ConnHandle -> PrimIO ()

%foreign (libpq "status")
ffi_status : ConnHandle -> PrimIO Int

%foreign (libpq "errorMessage")
ffi_errorMessage : ConnHandle -> PrimIO BorrowedString

%foreign (libpq "serverVersion")
ffi_serverVersion : ConnHandle -> PrimIO Int

export
data Conn : (0 s : Type) -> Type where
  MkConn : (handle : ConnHandle) -> Conn s

%name Conn conn

export
HandleWrapper ConnHandle Conn where
  getHandle (MkConn h) = h


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

export
status : HasIO io => (c : Conn s) -> io Int
status = wrapFFI ffi_status

export
errorMessage : HasIO io => (c : Conn s) -> io String
errorMessage = map asString . wrapFFI ffi_errorMessage

export
reset : HasIO io => (c : Conn s) -> io ()
reset = wrapFFI ffi_reset

export
serverVersion : HasIO io => (c : Conn s) -> io Int
serverVersion = wrapFFI ffi_serverVersion
