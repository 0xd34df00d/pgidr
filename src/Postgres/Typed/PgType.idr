module Postgres.Typed.PgType

%default total

%prefix_record_projections off

public export
PgTyParseError : Type
PgTyParseError = String

public export
record UnknownPgType where
  constructor MkUPT
  rawContents : String

public export
interface PgType ty where
  toTextual : ty -> String
  fromTextual : String -> Either PgTyParseError ty

public export
PgType String where
  toTextual = id
  fromTextual = pure

public export
PgType Int where
  toTextual = cast
  fromTextual = pure . cast -- TODO better error reporting

public export
PgType Integer where
  toTextual = cast
  fromTextual = pure . cast -- TODO better error reporting

public export
PgType UnknownPgType where
  toTextual = .rawContents
  fromTextual = pure . MkUPT
