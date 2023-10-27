module Postgres.Typed.InSignature

import Data.Vect.Quantifiers

import Postgres.Typed.PgType
import Postgres.Typed.Signature

%default total
%prefix_record_projections off

public export
data HasName : SignatureElem -> String -> Type where
  MkHN : PgType type => (name : String) -> HasName (MkSE name type modifiers) name

public export
InSignature : String -> Signature n -> Type
InSignature name sig = Any (`HasName` name) sig

public export
namesToIxes : HasSignature n ty =>
              {k : _} ->
              {names : Vect k String} ->
              (alls : All (`InSignature` signatureOf ty) names) ->
              Vect k (Fin n)
namesToIxes [] = []
namesToIxes (inSig :: inSigs) = anyToFin inSig :: namesToIxes inSigs
