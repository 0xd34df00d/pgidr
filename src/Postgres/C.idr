module Postgres.C

libpq : String -> String
libpq s = "C:PQ" <+> s <+> ",libpq"


BorrowedString : Type
BorrowedString = Ptr String

%foreign "C:strdup,libc"
c_strdup : Ptr String -> String

asString : BorrowedString -> String
asString = c_strdup


data ConnTag : Type where

Handle : Type
Handle = Ptr ConnTag

%foreign (libpq "connectdb")
ffi_connectdb : String -> PrimIO Handle

%foreign (libpq "finish")
ffi_finish : Handle -> PrimIO ()

%foreign (libpq "reset")
ffi_reset : Handle -> PrimIO ()

%foreign (libpq "status")
ffi_status : Handle -> PrimIO Int

%foreign (libpq "errorMessage")
ffi_errorMessage : Handle -> PrimIO BorrowedString

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

wrapFFI : HasIO io => (Handle -> PrimIO a) -> (c : Conn s) -> io a
wrapFFI ffi = primIO . ffi . getHandle

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
