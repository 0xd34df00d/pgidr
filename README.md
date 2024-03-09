**pgidr** — PostgreSQL bindings for Idris

This library provides both low-level wrappers around `libpq`,
as well as higher-level type-safe wrappers around basic SQL commands.

## A quick intro

### Creating tables

For an example of the latter, let's define a type representing a person:
```idris
import Postgres.Typed.Tuple

0 Person : (dir : Dir) -> Type
Person = NamedTuple "persons" [ PKeyInt "id"   -- a shortcut for a PRIMARY KEY that is SERIAL
                              , "first_name" @: String
                              , "last_name" @: String
                              , "age" @: Integer
                              , "home_phone" @:? String   -- ? marks a nullable field
                              ]
```
The `Dir` is a technicality to account for different types on reads/writes/updates to the same table:
for instance, a primary key or a `DEFAULT`ed value that is `NOT NULL`
is optional when storing a record to the database
but it's always present when reading it back,
so it is modeled by a `Maybe a` on writes and `a` on reads.

It is also a good idea to mark tables as runtime-irrelevant via `0` to ensure they are erased at compile-time.

Now we can create a table with `Person`s.
`Postgres.Typed.Operations.create` does the trick, so in any `HasIO` context, we can:
```idris
withConnection "user=pgidr_role dbname=pgidr_db" $ \conn => do
  result <- runMonadExec conn (create Person)
```
Here, `runMonadExec` executes an operation or a sequence of SQL operations,
and it is responsible for error reporting, among other things.
The `result` of `runMonadExec action` is a `Either ExecError res`,
where `res` is the result of the `action` (a `()` in this particular case).

### Inserting records

From now on, let's assume we're inside a `runMonadExec`:
```idris
runMonadExec conn $ do
  ...
```

Then, we can insert a few records into our DB:
```idris
runMonadExec conn $ do
  result <- execute $ insert into Person [ Nothing, "John", "Doe", 42, Nothing ]
```
The `result` here is also a `()`, since a plain `INSERT` query doesn't return anything.
Also note that we don't provide anything for the primary key, passing a `Nothing` instead:
PostgreSQL will generate it for us.

We can ask to return the primary key of the record we just inserted, though:
```idris
  janeId <- execute $ insert' into Person [ Nothing, "Jane", "Doe", 42, Just "555-55-55" ] { returning := column "id" }
```
and `johnId` here is an `Integer`
(so if we wrote `pure johnId` next and ended the `runMonadExec` block, we'd get an `Either ExecError Integer`).

We can also ask for more than one column:
```idris
  result <- execute $ insert' into Person [ Nothing, "John", "Doe", 42, Just "555-55-555" ] { returning := columns ["id", "first_name"] }
```
getting a tuple of the two corresponding elements, and it's perhaps easier to pattern-match it straight away:
```idris
  [johnId, johnName] <- execute $ insert' into Person [ Nothing, "John", "Doe", 42, Just "555-55-555" ] { returning := columns ["id", "first_name"] }
```
We can even ask for the whole row:
```idris
  johnDoeRow <- execute $ insert' into Person [ Nothing, "John", "Doe", 22, Nothing ] { returning := all }
```
getting a `Person` back!

### Queries are monadic too!

In fact, SQL queries and actions form a monadic structure as well, so the above could be written simply as
```idris
  johnId <- execute $ do
    () <- insert into Person [ Nothing, "John", "Doe", 42, Nothing ]
    janeId <- insert' into Person [ Nothing, "Jane", "Doe", 42, Just "555-55-55" ] { returning := column "id" }
    [johnId, johnName] <- insert' into Person [ Nothing, "John", "Doe", 42, Just "555-55-555" ] { returning := columns ["id", "first_name"] }
    wholeJohnDoeRow <- insert' into Person [ Nothing, "John", "Doe", 22, Nothing ] { returning := all }
    pure johnId
```
Of course, if any of the queries abort, the subsequent one won't be executed — just with anything else in a `MonadExec` action.

### Selects



### References

We can define a table that references our `Person`s:
```idris
0 Payout : (dir : Dir) -> Type
Payout = NamedTuple "payouts" [ PKeyInt "id"
                              , "person_id" @> Person $ "id"
                              , "payout_sum" @: Integer
                              ]
```
and then insert a few payouts (assuming we're continuing in the above `execute` `do`-block after `pure johnId`):
```
    for_ {t = List} [100, 300, 200, 400] $ \sum =>
      insert into Payout [ Nothing, janeId, sum ]
    for_ {t = List} [10, 30, 20, 40] $ \sum =>
      insert into Payout [ Nothing, johnId, sum ]
```

## Features

`INSERT`:

* [x] Basic inserts
* [x] `RETURNING`
* [ ] `ON CONFLICT`

`SELECT`:

* [x] Basic selects
* [x] `WHERE`
* [x] `ORDER BY`
* [x] `GROUP BY`
* [x] Inner joins
* [ ] Outer joins
* [ ] Aggregate functions
* [ ] Typecheck `GROUP BY` vs the `WHERE` clause
* [ ] Smart return type (`List ty` vs `ty` vs `Maybe ty`) calculation

`UPDATE`:

* [ ] Basic updates with `WHERE`

`DELETE`:

* [x] Basic deletes with `WHERE`
* [x] `RETURNING`

## Building

Assuming you have [pack](https://github.com/stefan-hoeck/idris2-pack) and PostgreSQL libraries installed,
```shell
pack build pgidr.ipkg
```
should do.

## Caveats and compromises

### Typed pq functions

Certain PostgreSQL API functions (in particular `PQexecParams` and `PQprepare`)
allow passing the (PostgreSQL) types of the query parameters.
When the types are missing, the server derives those from the context.

We've chosen to _not_ expose these types in the API,
as the added clumsiness and complexity doesn't seem to be justified by the benefits.
Please let us know if your use case requires
explicit passing of the types to the PostgreSQL server.
