module Control.Syntax

import Data.List

%default total

infix 1 ~>
public export
(~>) : a -> b -> (a, b)
(~>) = (,)

public export
otherwise : a -> a
otherwise = id

public export
contains : List a -> List (a -> Bool, r) -> r -> r
contains xs [] fallback = fallback
contains xs ((test, res) :: tests) fallback =
  case find test xs of
       Just _ => res
       Nothing => contains xs tests fallback
