**pgidr** — PostgreSQL bindings for Idris

This library provides both low-level wrappers around `libpq`,
as well as higher-level type-safe wrappers around basic SQL commands.

## A quick intro

For an example of the latter, let's define a type representing a person:
```idris
import Postgres.Typed.Tuple

Person : Dir -> Type
Person = NamedTuple "persons" [ MkSE "id" Integer [PKey PKeySerial]
                              , "first_name" @: String
                              , "last_name" @: String
                              , "age" @: Integer
                              ]
```
The `Dir` is a technicality to account for different types on reads/writes/updates to the same table:
for instance, a primary key or a `DEFAULT`ed value that is `NOT NULL`
is optional when storing a record to the database
but it's always present when reading it back,
so it is modeled by a `Maybe a` on writes and `a` on reads.

Now we can create a table with `Person`s.
`Postgres.Typed.Operations.create` does the trick, so in any `HasIO` context, we can:
```idris
withConnection "user=pgidr_role dbname=pgidr_db" $ \conn => do
  result <- runMonadExec (create conn Person)
```
Here, `runMonadExec` executes an operation (that is, a `MonadExec` action),
and it is responsible for error reporting, among other things.
The `result` of `runMonadExec action` is a `Either ExecError res`,
where `res` is the original result of the action (a `()` in this particular case).

### Inserting records

Then, we can insert a few records into our DB:
```idris
  let query = insert into Person [ Nothing, "John", "Doe", 42 ]
  result <- execute' conn query
```
Here, `execute'` is another shortcut for executing `MonadExec` actions.
The `result` here is also `Either ExecError ()`,
since a plain `INSERT` query doesn't return anything.

We can ask it to return the primary key of the record we just inserted, though:
```idris
  let query = insert' into Person [ Nothing, "John", "Doe", 42 ] { returning := column "id" }
  result <- execute' conn query
```
and `result` here is an `Either ExecError Integer`.
We can ask for more than one column:
```idris
  let query = insert' into Person [ Nothing, "John", "Doe", 42 ] { returning := columns ["id", "first_name"] }
  result <- execute' conn query
```
or even the whole row:
```idris
  let query = insert' into Person [ Nothing, "John", "Doe", 22 ] { returning := all }
  result <- execute' conn query
```
The types of the corresponding `result`s will be just as you'd expect!

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
