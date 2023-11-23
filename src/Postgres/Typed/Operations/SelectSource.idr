module Postgres.Typed.Operations.SelectSource

import Postgres.Typed.Tuple

%default total

public export
interface IsSelectSource (0 ty : a) where
  constructor MkSelectSource
  selectSource : String

public export
selectSourceOf : (0 ty : a) ->
                 IsSelectSource ty =>
                 String
selectSourceOf ty = selectSource {ty}

public export
HasTableName ty => IsSelectSource ty where
  selectSource = tableNameOf ty
