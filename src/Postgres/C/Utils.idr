module Postgres.C.Utils

import Data.Buffer as B
import Data.DPair
import Data.List
import Data.Vect

%default total

public export
libpq : String -> String
libpq s = "C:PQ" <+> s <+> ",libpq"


public export
BorrowedString : Type
BorrowedString = Ptr String

%foreign "C:strdup,libc"
c_strdup : BorrowedString -> String

export
asString : BorrowedString -> String
asString = c_strdup


public export
interface HandleWrapper (0 raw : Type) (0 wrapper : (0 _ : Type) -> Type) | wrapper where
  getHandle : wrapper s -> raw

export
wrapFFI : (HasIO io, HandleWrapper rawHandle wrappedHandle) =>
          (rawHandle -> PrimIO a) ->
          (c : wrappedHandle s) ->
          io a
wrapFFI ffi = primIO . ffi . getHandle

export
wrapFFIpure : HandleWrapper rawHandle wrappedHandle =>
              (rawHandle -> a) ->
              (c : wrappedHandle s) ->
              a
wrapFFIpure ffi = ffi . getHandle

export
forTo : (Applicative f, Num n, Ord n, Range n) => (start, end : n) -> (n -> f b) -> f (List b)
forTo start end f =
  if start >= end
     then pure []
     else for (fromMaybe [] $ init' [start .. end]) f

export
forTo_ : (Applicative f, Num n, Ord n, Range n) => (start, end : n) -> (n -> f b) -> f ()
forTo_ start end f = forTo start end f $> ()


%foreign "C:setStrArrayItem,libpgidr-cbits"
ffi_setStrArrayItem : (buf : Buffer) -> (index : Int) -> (val : String) -> PrimIO ()

setStrArrayItem : HasIO io => (buf : Buffer) -> (index : Int) -> (val : String) -> io ()
setStrArrayItem buf index val = primIO $ ffi_setStrArrayItem buf index val

%foreign "C:ptrSize,libpgidr-cbits"
ffi_ptrSize : Int

export
toStringArray : HasIO io =>
                {n : _} ->
                (params : Vect n (Maybe String)) ->
                io (Maybe Buffer)
toStringArray params = do
  let bytesInPtr = 8
  Just buf <- B.newBuffer (cast n * ffi_ptrSize)
    | Nothing => pure Nothing
  flip traverse_ (zip (tabulate fst) params) $ \(i, maybeStr) => do
    case maybeStr of
         Just str => setStrArrayItem buf (cast i) str
         Nothing => pure ()
  pure $ Just buf
