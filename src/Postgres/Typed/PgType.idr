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

Show UnknownPgType where
  show = const "<unknown>"

public export
interface Show ty => PgType ty where
  toTextual : ty -> String
  fromTextual : String -> Either PgTyParseError ty

public export
data SomePgType : Type where
  MkSomePgType : (ty : Type) -> PgType ty => SomePgType

public export
PgType String where
  toTextual = id
  fromTextual = pure

public export
PgType Integer where
  toTextual = cast
  fromTextual = pure . cast -- TODO better error reporting

public export
PgType Bool where
  toTextual True = "1"
  toTextual False = "0"
  fromTextual str = if str `elem` trues then pure True
                    else if str `elem` falses then pure False
                    else Left $ "unable to parse `" ++ str ++ "` as a boolean"
    where
    trues, falses : List String
    trues = ["1", "true", "yes", "on"]
    falses = ["0", "false", "no", "off"]

public export
PgType UnknownPgType where
  toTextual = .rawContents
  fromTextual = pure . MkUPT


public export
interface PgType ty => CreatablePgType ty where
  fieldTypeName : String

public export
fieldTypeNameOf : (0 ty : Type) -> CreatablePgType ty => String
fieldTypeNameOf ty = fieldTypeName {ty}

public export
CreatablePgType String where
  fieldTypeName = "TEXT"

public export
CreatablePgType Integer where
  fieldTypeName = "INTEGER"

public export
CreatablePgType Bool where
  fieldTypeName = "BOOLEAN"
