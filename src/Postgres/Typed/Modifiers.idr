module Postgres.Typed.Modifiers

import Postgres.Typed.PgType
import Postgres.Typed.Signature

%default total
%prefix_record_projections off

public export
record PKey (ty : Type) where
  constructor MkPKey
  val : ty

public export
Show ty => Show (PKey ty) where
  show pk = "PK(" ++ show (pk.val) ++ ")"

public export
PgType ty => PgType (PKey ty) where
  toTextual = toTextual . .val
  fromTextual = map MkPKey . fromTextual


public export
record References (sig : Signature n) (idx : Fin n) where
  constructor MkReferences
  isNotNull : (idx `index` sig).isNull = NonNullable
  val : (idx `index` sig).type

public export
Show (idx `index` sig).type => Show (References sig idx) where
  show ref = "Ref(" ++ show (ref.val) ++ ")"

public export
ValidRefTarget : SignatureElem -> Type
ValidRefTarget elem = (PgType elem.type, elem.isNull = NonNullable)

public export
ValidRefTarget (idx `index` sig) => PgType (References sig idx) where
  toTextual = toTextual . (.val)
  fromTextual = map (MkReferences %search) . fromTextual
