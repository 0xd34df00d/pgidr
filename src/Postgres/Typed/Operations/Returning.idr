module Postgres.Typed.Operations.Returning

import Postgres.C

import Postgres.Typed.MonadExec
import public Postgres.Typed.Tuple
import Postgres.Typed.Operations.Helpers

%default total
%prefix_record_projections off

public export
0
typeAt : (0 ty : OpCtx -> Type) ->
         HasSignature Unqualified n ty =>
         (idx : Fin n) ->
         Type
typeAt ty idx = computeType' Read (idx `index` signatureOf ty)

public export
data RowCount = OneRow | ManyRows

public export
0
applyRowCount : RowCount -> Type -> Type
applyRowCount OneRow ty = ty
applyRowCount ManyRows ty = List ty

public export
data Columns : (cnt : RowCount) -> (ty : OpCtx -> Type) -> (ret : Type) -> Type where
  CNone : Columns cnt ty ()
  CAll  : {n : _} ->
          IsTupleLike Unqualified n ty =>
          Columns cnt ty (applyRowCount cnt (ty Read))
  COne  : {n : _} ->
          IsTupleLike Unqualified n ty =>
          (idx : Fin n) ->
          Columns cnt ty (applyRowCount cnt $ typeAt ty idx)
  CSome : {n, k : _} ->
          IsTupleLike Unqualified n ty =>
          (idxes : Vect (S k) (Fin n)) ->
          Columns cnt ty (applyRowCount cnt $ subTuple ty idxes Read)

public export
all : {n : _} ->
      IsTupleLike Unqualified n ty =>
      Columns cnt ty (applyRowCount cnt $ ty Read)
all = CAll

public export
ColsType : (ty : OpCtx -> Type) ->
           IsTupleLike Unqualified n ty =>
           {k : _} ->
           {names : Vect k (Name Unqualified)} ->
           (alls : All (`InSignature` signatureOf ty) names) ->
           Type
ColsType ty alls = Tuple (signatureOf ty `subSignature` namesToIxes alls) Read

public export
columns : {n : _} ->
          IsTupleLike Unqualified n ty =>
          {k : _} ->
          (names : Vect (S k) (Name Unqualified)) ->
          {auto alls : All (`InSignature` signatureOf ty) names} ->
          Columns cnt ty (applyRowCount cnt $ ColsType ty alls)
columns _ = CSome $ namesToIxes alls

public export
column : {n : _} ->
         IsTupleLike Unqualified n ty =>
         (name : Name Unqualified) ->
         {auto inSig : name `InSignature` signatureOf ty} ->
         Columns cnt ty (applyRowCount cnt $ computeType' Read (inSigToFin inSig `index` signatureOf ty))
column _ = COne $ inSigToFin inSig

export
toColumnNames : Columns cnt ty ret -> Maybe (List String)
toColumnNames CNone = Nothing
toColumnNames CAll = Just $ map (.uname) $ toList $ allColumnNames ty
toColumnNames (COne idx) = Just [(idx `index` signatureOf ty).name.uname]
toColumnNames (CSome idxes) = Just $ map (.uname) $ toList $ columnNames ty idxes

export
mkReturningClause : (returning : Columns cnt ty ret) -> String
mkReturningClause = maybe "" (\cols => "RETURNING " ++ joinBy ", " cols) . toColumnNames

infixl 1 =<<|
(=<<|) : Monad m => ((0 _ : a) -> m b) -> m a -> m b
f =<<| act = act >>= \r => f r

extractFirstRow : MonadError ExecError m =>
                  {n : _} ->
                  (res : Result s) ->
                  (sig : Signature Unqualified n) ->
                  (0 matches : ResultMatches res sig 1) ->
                  m (Tuple sig Read)
extractFirstRow res sig matches = extractFields res (rewrite matches.rowsMatch in 0) sig matches

export
extractReturning : MonadError ExecError m =>
                   {cnt : _} ->
                   Result s ->
                   Columns cnt ty ret ->
                   m ret
extractReturning {cnt = OneRow} result = \case
   CNone => pure ()
   CAll => fromTuple <$> (extractFirstRow result _ =<<| ensureMatches)
   COne idx => head <$> (extractFirstRow result (subSignature _ [idx]) =<<| ensureMatches)
   CSome idxes => extractFirstRow result _ =<<| ensureMatches
extractReturning {cnt = ManyRows} result = \case
   CNone => pure ()
   CAll => map fromTuple <$> extractFieldsMany result _
   COne idx => map head <$> extractFieldsMany result (subSignature _ [idx])
   CSome idxes => extractFieldsMany result _
