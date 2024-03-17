module Postgres.Typed.Operations.Returning

import Postgres.C

import Postgres.Typed.MonadExec
import public Postgres.Typed.Tuple
import Postgres.Typed.Operations.Helpers

%default total
%prefix_record_projections off

public export
0
typeAt : (0 tbl : Table n) ->
         (idx : Fin n) ->
         Type
typeAt tbl idx = computeType' Read (idx `index` tbl.signature)

public export
data RowCount = OneRow | ManyRows

public export
0
applyRowCount : RowCount -> Type -> Type
applyRowCount OneRow ty = ty
applyRowCount ManyRows ty = List ty

public export
data Columns : (cnt : RowCount) -> (tbl : Table n) -> (ret : Type) -> Type where
  CNone : Columns cnt tbl ()
  CAll  : {n : _} ->
          {tbl : Table n} ->
          Columns cnt tbl (applyRowCount cnt $ tableTuple tbl Read)
  COne  : {n : _} ->
          {tbl : Table n} ->
          (idx : Fin n) ->
          Columns cnt tbl (applyRowCount cnt $ typeAt tbl idx)
  CSome : {n, k : _} ->
          {tbl : Table n} ->
          (idxes : Vect (S k) (Fin n)) ->
          Columns cnt tbl (applyRowCount cnt $ subTuple tbl idxes Read)

public export
all : {n : _} ->
      {tbl : Table n} ->
      Columns cnt tbl (applyRowCount cnt $ tableTuple tbl Read)
all = CAll

public export
0
ColsType : (tbl : Table n) ->
           {k : _} ->
           {names : Vect k (Name Unqualified)} ->
           (alls : All (`InSignature` tbl.signature) names) ->
           Type
ColsType tbl alls = Tuple (tbl.signature `subSignature` namesToIxes alls) Read

public export
columns : {n, k : _} ->
          {tbl : Table n} ->
          (names : Vect (S k) (Name Unqualified)) ->
          {auto alls : All (`InSignature` tbl.signature) names} ->
          Columns cnt tbl (applyRowCount cnt $ ColsType tbl alls)
columns _ = CSome $ namesToIxes alls

public export
column : {n : _} ->
         {tbl : Table n} ->
         (name : Name Unqualified) ->
         {auto inSig : name `InSignature` tbl.signature} ->
         Columns cnt tbl (applyRowCount cnt $ typeAt tbl (inSigToFin inSig))
column _ = COne $ inSigToFin inSig

export
toColumnNames : Columns cnt tbl ret ->
                Maybe (List String)
toColumnNames CNone = Nothing
toColumnNames CAll = Just $ map (.uname) $ toList $ allColumnNames tbl.signature
toColumnNames (COne idx) = Just [(idx `index` tbl.signature).name.uname]
toColumnNames (CSome idxes) = Just $ map (.uname) $ toList $ columnNames (tbl.signature) idxes

export
mkReturningClause : (returning : Columns cnt tbl ret) ->
                    String
mkReturningClause = maybe "" (\cols => "RETURNING " ++ joinBy ", " cols) . toColumnNames

infixl 1 =<<|
(=<<|) : Monad m => ((0 _ : a) -> m b) -> m a -> m b
f =<<| act = act >>= \r => f r

extractFirstRow : MonadError ExecError m =>
                  (res : Result s) ->
                  (sig : Signature Unqualified n) ->
                  (0 matches : ResultMatches res sig 1) ->
                  m (Tuple sig Read)
extractFirstRow res sig matches = extractFields res (rewrite matches.rowsMatch in 0) sig matches

export
extractReturning : MonadError ExecError m =>
                   {cnt : _} ->
                   Result s ->
                   Columns cnt tbl ret ->
                   m ret
extractReturning {cnt = OneRow} result = \case
   CNone => pure ()
   CAll => extractFirstRow result _ =<<| ensureMatches
   COne idx => head <$> (extractFirstRow result (subSignature _ [idx]) =<<| ensureMatches)
   CSome idxes => extractFirstRow result _ =<<| ensureMatches
extractReturning {cnt = ManyRows} result = \case
   CNone => pure ()
   CAll => extractFieldsMany result _
   COne idx => map head <$> extractFieldsMany result (subSignature _ [idx])
   CSome idxes => extractFieldsMany result _
