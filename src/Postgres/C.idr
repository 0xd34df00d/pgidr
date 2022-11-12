module Postgres.C

data PG : Type where

libpq : String -> String
libpq s = "C:PQ" <+> s <+> ",libpq"

Handle : Type
Handle = Ptr PG

%foreign (libpq "connectdb")
ffi_connectdb : String -> PrimIO Handle

%foreign (libpq "finish")
ffi_finish : Handle -> PrimIO ()

%foreign (libpq "reset")
ffi_reset : Handle -> PrimIO ()

%foreign (libpq "status")
ffi_status : Handle -> PrimIO Int

%foreign (libpq "serverVersion")
ffi_serverVersion : Handle -> PrimIO Int


export
data Conn : (0 s : Type) -> Type where
  MkConn : (handle : Handle) -> Conn s

%name Conn conn

getHandle : Conn s -> Handle
getHandle (MkConn handle) = handle


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
status = primIO . ffi_status . getHandle

export
reset : HasIO io => (c : Conn s) -> io ()
reset = primIO . ffi_reset . getHandle

export
serverVersion : HasIO io => (c : Conn s) -> io Int
serverVersion = primIO . ffi_serverVersion . getHandle
