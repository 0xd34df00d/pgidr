module Postgres.Example

import Data.List
import Data.Vect
import Postgres.C

import Postgres.Typed.Modifiers
import Postgres.Typed.Signature
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
  res <- exec conn "DROP TABLE IF EXISTS payouts"
  res <- exec conn "DROP TABLE IF EXISTS persons"
  dumpResult res

0 Person : (dir : Dir) -> Type
Person = NamedTuple "persons" [PKeyInt "id", "first_name" @: String, "last_name" @: String, "age" @: Integer]

0 Payout : (dir : Dir) -> Type
Payout = NamedTuple "payouts" [PKeyInt "id", "person_id" @> Person $ "id", "payout_sum" @: Integer]

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
  res <- runMonadExec $ do
    create conn Person
    create conn Payout

    execute conn $ do
      () <- insert into Person [ Nothing, "John", "Doe", 42 ]
      p2 <- insert' into Person [ Nothing, "Jane", "Doe", 32 ] { returning := all }
      p3id <- insert' into Person [ Nothing, "Johnny", "Donny", 41 ] { returning := column "id" }
      [p4id, _] <- insert' into Person [ Nothing, "Foo", "Bar", 666 ] { returning := columns ["id", "first_name"] }

      for_ {t = List} [100, 300, 200, 400] $ \sum =>
        insert into Payout [ Nothing, p3id, sum ]
      for_ {t = List} [10, 30, 20, 40] $ \sum =>
        insert into Payout [ Nothing, p4id, sum ]

      allPersons <- select from Person id
      allDoes <- select from Person { whereClause := col "last_name" == "Doe", orderBy := "first_name" }
      _ <- select from (Person `as` "p1" `crossJoin` Person `as` "p2") id
      pure ()
    payouts <- execute conn (select from (innerJoin (table Person) (table Payout) $ "payouts"."person_id" == "persons"."id") id)
    print payouts
  case res of
       Left err => putStrLn $ "error: " ++ show err
       Right _ => putStrLn "all good!"
