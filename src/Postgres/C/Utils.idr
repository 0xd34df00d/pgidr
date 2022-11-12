module Postgres.C.Utils

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
