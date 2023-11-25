module Postgres.Example

import Data.List
import Data.Vect
import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.Tuple

import Postgres.Typed.Operations
import Postgres.Typed.Operations.Join

dumpResult : HasIO io => Result s -> io ()
dumpResult res = do
  resultStatus res >>= printLn
  resultErrorMessage res >>= putStr

dropTable : HasIO io => Conn s -> io ()
dropTable conn = do
  putStrLn "dropping table..."
  res <- exec conn "DROP TABLE IF EXISTS persons"
  dumpResult res

Person : (dir : Dir) -> Type
Person = NamedTuple "persons" [Serial "id", "first_name" @: String, "last_name" @: String, "age" @: Integer]

handleResult : Show res => String -> Either ExecError res -> IO ()
handleResult success = \case Left err => putStrLn $ "error: " ++ show err
                             Right r => putStrLn $ success ++ ": " ++ show r

{-
Assuming you've run
```
CREATE USER pgidr_role;
CREATE DATABASE pgidr_db OWNER pgidr_role;
```
in `psql`.
-}
export
example : IO ()
example = withConnection "user=pgidr_role dbname=pgidr_db" $ \conn => do
  s <- status conn
  v <- serverVersion conn
  printLn (s, v)
  e <- errorMessage conn
  putStr e

  dropTable conn
  runMonadExec (create conn Person) >>= handleResult "created persons"

  execute' conn (insert into Person [ Nothing, "John", "Doe", 42 ])
    >>= handleResult "inserted person 1"
  execute' conn (insert' into Person [ Nothing, "Jane", "Doe", 32 ] { returning := all })
    >>= handleResult "inserted person 2"
  execute' conn (insert' into Person [ Nothing, "Johnny", "Donny", 41 ] { returning := column "id" })
    >>= handleResult "inserted person 3"
  execute' conn (insert' into Person [ Nothing, "Foo", "Bar", 666 ] { returning := columns ["id", "first_name"] })
    >>= handleResult "inserted person 4"

  execute' conn (select from Person id) >>= handleResult "selected all persons"
  execute' conn (select from Person { whereClause := col "last_name" == "Doe", orderBy := "first_name" }) >>= handleResult "selected all persons"
  execute' conn (select from (Person `as` "p1" `crossJoin` Person `as` "p2") id) >>= handleResult "selected all persons"
