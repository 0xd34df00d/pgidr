module Postgres.Typed.Modifiers

import Postgres.Typed.PgType
import Postgres.Typed.Signature

%default total

public export
record PKey (ty : Type) where
  constructor MkPKey
  pkVal : ty

public export
Show ty => Show (PKey ty) where
  show pk = "PK(" ++ show (pk.pkVal) ++ ")"

public export
PgType ty => PgType (PKey ty) where
  toTextual = toTextual . .pkVal
  fromTextual = map MkPKey . fromTextual


public export
record References (sig : Signature n) (idx : Fin n) where
  constructor MkReferences
  isNotNull : (idx `index` sig).isNull = NonNullable
  refVal : (idx `index` sig).type

public export
Show (idx `index` sig).type => Show (References sig idx) where
  show ref = "Ref(" ++ show (ref.refVal) ++ ")"

public export
(PgType (idx `index` sig).type, (idx `index` sig).isNull = NonNullable) => PgType (References sig idx) where
  toTextual = toTextual . (.refVal)
  fromTextual = map (MkReferences %search) . fromTextual
