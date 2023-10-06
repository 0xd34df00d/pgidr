module Postgres.Example

import Data.List
import Data.Vect
import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.Tuple

import Postgres.Typed.Operations

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
Person = NamedTuple "persons" [MkSE "id" Integer [PKey PKeySerial], "first_name" @: String, "last_name" @: String, "age" @: Integer]

samplePerson : Person Write
samplePerson = MkTup [ Just 1, "John", "Doe", 42 ]

handleResult : (Show res, HasIO io) => String -> Either String res -> io ()
handleResult success = \case Left err => putStrLn err
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
  create conn Person >>= handleResult "created persons"

  execute conn (insert into Person $ MkTup [ Nothing, "John", "Doe", 42 ]) >>= handleResult "inserted person"
  --printLn $ toQuery $ select from Person { fields := FieldsAll }

{-
  let insertQuery = "INSERT INTO persons (first_name, last_name, age, country) VALUES ($1, $2, $3, $4)"

  putStrLn "inserting..."
  execParams conn insertQuery [Just "John", Just "Doe", Just "42", Nothing] >>= dumpResult

  putStrLn "preparing..."
  prepare conn "inserter" insertQuery >>= dumpResult

  putStrLn "inserting more..."
  execPrepared conn "inserter" [Just "Jane", Just "Doe", Just "36", Just "us"] >>= dumpResult
  execPrepared conn "inserter" [Just "Uncle", Just "Bob", Just "10", Nothing] >>= dumpResult

  putStrLn "querying..."
  res <- exec conn "SELECT * FROM persons"
  dumpResult res

  putStrLn "shape:"
  let fieldsCnt = nfields res
      rowsCnt = ntuples res
  printLn (rowsCnt, fieldsCnt)

  putStrLn "names:"
  forTo_ 0 fieldsCnt $ printLn . fname res

  putStrLn "formats:"
  forTo_ 0 fieldsCnt $ printLn . fformat res

  putStrLn "mods:"
  forTo_ 0 fieldsCnt $ printLn . fmod res

  putStrLn "types:"
  forTo_ 0 fieldsCnt $ printLn . ftype res
  -}
