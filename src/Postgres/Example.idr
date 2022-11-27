module Postgres.Example

import Postgres.C

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

  putStrLn "querying..."
  res <- exec conn "SELECT * FROM persons"
  dumpResult res

  putStrLn "shape:"
  fieldsCnt <- nfields res
  rowsCnt <- ntuples res
  printLn (rowsCnt, fieldsCnt)

  putStrLn "formats:"
  flip traverse [0 .. fieldsCnt - 1] (fformat res) >>= printLn

  putStrLn "mods:"
  flip traverse [0 .. fieldsCnt - 1] (fmod res) >>= printLn

  putStrLn "types:"
  flip traverse [0 .. fieldsCnt - 1] (ftype res) >>= printLn

  putStrLn "values:"
  flip traverse_ [0 .. rowsCnt - 1] $ \row => do
    putStr "| "
    flip traverse_ [0 .. fieldsCnt - 1] $ \col => do
      getvalueTextual res row col >>= putStr
      putStr " | "
    putStrLn ""
