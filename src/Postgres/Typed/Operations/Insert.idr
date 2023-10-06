module Postgres.Typed.Operations.Insert

import Data.String
import Data.Vect

import Postgres.C

import public Postgres.Typed.Tuple
import Postgres.Typed.Util

import Postgres.Typed.Operations.Class

%default total
%prefix_record_projections off

mapProperty' : {xs : Vect n a} ->
               (f : (x : a) -> p x -> q x) ->
               All p xs ->
               All q xs
mapProperty' f [] = []
mapProperty' f (x :: xs) = f _ x :: mapProperty' f xs

record InsertColumn where
  constructor MkIC
  colName : String
  value : String

mkInsertQuery : {k : _} ->
                {0 ty : _} ->
                HasSignature n ty =>
                (cols : Vect k InsertColumn) ->
                String
mkInsertQuery cols =
  let namesStr = joinBy ", " $ toList $ .colName <$> cols
      placeholders = joinBy ", "
                   $ toList
                   $ tabulate {len = k} (\i => "$" ++ show (finToNat i + 1))
   in "INSERT INTO \{tableNameOf ty} (\{namesStr}) VALUES (\{placeholders})"

mkInsertColumns : IsRecordType n ty =>
                  (val : ty Write) ->
                  (k ** Vect k InsertColumn)
mkInsertColumns = catMaybes
                . forget
                . mapProperty' (\se => onSigValUniform (MkIC se.name . toTextual) se)
                . columns
                . toTuple

namespace Fields
  public export
  data Fields : (ty : a) -> Type where
    FieldsNone : Fields ty
    FieldsAll  : HasSignature n ty => Fields ty
    FieldsSome : HasSignature n ty =>
                 (ixes : Vect k (Fin n)) ->
                 Fields ty

  export
  all : HasSignature n ty => Fields ty
  all = FieldsAll

  public export
  data HasName : SignatureElem -> String -> Type where
    MkHN : PgType type => (name : String) -> HasName (MkSE name type modifiers) name

  public export
  InSignature : String -> Signature n -> Type
  InSignature name sig = Any (`HasName` name) sig

  anyToFin : {0 xs : Vect n _} -> Any p xs -> Fin n
  anyToFin (Here _) = FZ
  anyToFin (There later) = FS (anyToFin later)

  export
  fields : HasSignature n ty =>
          (names : Vect k String) ->
          {auto alls : All (`InSignature` signatureOf ty) names} ->
          Fields ty
  fields names {alls} = FieldsSome $ go alls
    where
    go : {0 names' : Vect k' String} ->
         (All (`InSignature` signatureOf ty) names') ->
         Vect k' (Fin n)
    go [] = []
    go (inSig :: inSigs) = anyToFin inSig :: go inSigs


public export
record Insert (ty : Dir -> Type) where
  constructor MkInsert
  tyIsRecord : IsRecordType fieldsCount ty    -- TODO make auto implicit when Idris2#3083 is fixed
  value : ty Write

data DInto : Type where
public export
into : Dummy DInto
into = MkDF

namespace InsertRecord
  export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           IsRecordType n ty =>
           (val : ty Write) ->
           Insert ty
  insert _ _ val = MkInsert %search val

  export
  insert' : Dummy DInto ->
            (ty : Dir -> Type) ->
            {n : _} ->
            IsRecordType n ty =>
            (val : ty Write) ->
            (Insert ty -> Insert ty) ->
            Insert ty
  insert' d ty val f = f (insert d ty val)

namespace InsertTuple
  export
  insert : Dummy DInto ->
           (ty : Dir -> Type) ->
           {n : _} ->
           IsRecordType n ty =>
           (val : Tuple (signatureOf ty) Write) ->
           Insert ty
  insert d ty = insert d ty . fromRawTuple

  export
  insert' : Dummy DInto ->
            (ty : Dir -> Type) ->
            {n : _} ->
            IsRecordType n ty =>
            (val : Tuple (signatureOf ty) Write) ->
            (Insert ty -> Insert ty) ->
            Insert ty
  insert' d ty val f = insert' d ty (fromRawTuple val) f

export
Operation (Insert ty) where
  returnType _ = ()
  execute conn (MkInsert _ val) =
    let (_ ** cols) = mkInsertColumns val
        query = mkInsertQuery {ty} cols
        params = map (Just . .value) cols
     in execParams conn query params >>= checkStatus
