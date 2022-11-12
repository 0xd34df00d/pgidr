module Postgres.C

import Control.Linear.LIO

data PG : Type where

export
Conn : Type
Conn = Ptr PG

libpq : String -> String
libpq s = "C:PQ" <+> s <+> ",libpq"

%foreign (libpq "connectdb")
ffi_connectdb : String -> PrimIO Conn

%foreign (libpq "finish")
ffi_finish : Conn -> PrimIO ()

%foreign (libpq "status")
ffi_status : Conn -> PrimIO Int

export
withConnection : LinearIO io => (connStr : String) -> (1 f : (1 c : Conn) -> L io a) -> L io a
withConnection connStr f = do
  conn <- primIO $ ffi_connectdb connStr
  res <- f conn
  primIO $ ffi_finish conn
  pure res

export
status : LinearIO io => (1 c : Conn) -> L io (Int, Conn)
status = assert_linear (\c => map (, c) $ primIO $ ffi_status c)

export
example : IO Int
example = run $ withConnection "" $ \conn => do
  (s1, conn') <- status conn
  fst <$> status conn'
