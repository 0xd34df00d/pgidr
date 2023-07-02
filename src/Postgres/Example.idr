module Postgres.Example

import Data.Vect
import Postgres.C

import Postgres.Typed.Schema

dumpResult : HasIO io => Result s -> io ()
dumpResult res = do
  resultStatus res >>= printLn
  resultErrorMessage res >>= putStr

dropTable : HasIO io => Conn s -> io ()
dropTable conn = do
  putStrLn "dropping table..."
  res <- exec conn "DROP TABLE IF EXISTS persons"
  dumpResult res

createTable : HasIO io => Conn s -> io ()
createTable conn = do
  putStrLn "creating table..."
  res <- exec conn "CREATE TABLE persons (pid SERIAL PRIMARY KEY, first_name TEXT NOT NULL, last_name TEXT NOT NULL, age INTEGER NOT NULL, country TEXT)"
  dumpResult res

Person : Type
Person = Tuple ["first_name" @: String, "last_name" @: String, "age" @: Integer]

sampleName : Person
sampleName = [ "John", "Doe", 42 ]

Person' : Type
Person' = Tuple ["first_name" @: String, "last_name" @: String, "age" @:? Integer]

sampleName' : Person'
sampleName' = [ "John", "Doe", Just 42 ]

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
  createTable conn

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

  putStrLn "values:"
  forTo_ 0 rowsCnt $ \row => do
    putStr "| "
    forTo_ 0 fieldsCnt $ \col => do
      putStr $ getvalueTextual res row col
      putStr " | "
    putStrLn ""

  printLn $ fullResultSet defLookup res
