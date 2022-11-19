module Postgres.C.Utils

%default total

public export
libpq : String -> String
libpq s = "C:PQ" <+> s <+> ",libpq"


public export
BorrowedString : Type
BorrowedString = Ptr String

%foreign "C:strdup,libc"
c_strdup : BorrowedString -> String

export
asString : BorrowedString -> String
asString = c_strdup


public export
interface HandleWrapper (0 raw : Type) (0 wrapper : (0 _ : Type) -> Type) | wrapper where
  getHandle : wrapper s -> raw

export
wrapFFI : (HasIO io, HandleWrapper raw wrapper) =>
          (raw -> PrimIO a) ->
          (c : wrapper s) ->
          io a
wrapFFI ffi = primIO . ffi . getHandle
