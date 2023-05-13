module Postgres.Typed.PgType

%default total

%prefix_record_projections off

public export
record UnknownPgType where
  constructor MkUPT
  rawContents : String

public export
interface PgType ty where
  toTextual : ty -> String
  fromTextual : String -> Either String ty
  decEqTy : (ty' : Type) -> Dec (ty = ty')

-- TODO consider whether it's possible to prove these without believe_me
public export
PgType String where
  toTextual = id
  fromTextual = pure

  decEqTy String = Yes Refl
  decEqTy _ = No believe_me

public export
PgType Int where
  toTextual = cast
  fromTextual = pure . cast -- TODO better error reporting

  decEqTy Int = Yes Refl
  decEqTy _ = No believe_me

public export
PgType UnknownPgType where
  toTextual = .rawContents
  fromTextual = pure . MkUPT

  decEqTy UnknownPgType = Yes Refl
  decEqTy _ = No believe_me
