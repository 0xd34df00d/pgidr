module Postgres.Typed.Select

import public Postgres.Typed.Tuple

%default total

public export
data Fields : (ty : Type) -> Type where
  FieldsAll  : IsTableType _ ty => Fields ty
  FieldsSome : IsTableType n ty =>
               (ixes : Vect k (Fin n)) ->
               Fields ty

public export
data Order : (ty : Type) -> Type where
  OrderNone : Order ty

public export
record Select (ty : Type) where
  constructor MkSelect
  isTableType : IsTableType colCount ty
  fields : Fields ty
  orderby : Order ty

fieldsToString : Fields ty -> String
fieldsToString fields = case fields of
                             FieldsAll => toString $ signatureOf ty
                             FieldsSome ixes => toString $ (`index` signatureOf ty) <$> ixes
  where
  toString : Vect n SignatureElem -> String
  toString = concat . intersperse ", " . map columnName

data DummyTag = DFrom
record Dummy (tag : DummyTag) where
  constructor MkDF
public export
from : Dummy DFrom
from = MkDF

public export
select : Dummy DFrom ->
         (ty : Type) ->
         IsTableType n ty =>
         (Select ty -> Select ty) ->
         Select ty
select _ ty f = f (MkSelect %search FieldsAll OrderNone)


public export
toQuery : Select ty ->
          String
toQuery (MkSelect _ fields order) =
  "SELECT " ++ fieldsToString fields ++
  " FROM " ++ tableNameOf ty
