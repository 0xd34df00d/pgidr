**pgidr** — PostgreSQL bindings for Idris

This library provides both low-level wrappers around `libpq`,
as well as higher-level type-safe wrappers around basic SQL commands.

## A quick intro

For an example of the latter, let's define a type representing a person:
```idris
import Postgres.Typed.Tuple

Person : Dir -> Type
Person = NamedTuple "persons" [MkSE "id" Integer [PKey PKeySerial], "first_name" @: String, "last_name" @: String, "age" @: Integer]
```
The `Dir`{.idris} is a technicality to account for different types on reads/writes/updates to the same table:
for instance, a primary key or a `DEFAULT`{.sql}ed value that is `NOT NULL`{.sql}
is optional when adding a record but it's always present when reading,
so it is modeled by a `Maybe a`{.idris} on writes and `a`{.idris} on reads.

Now we can create a table with `Person`{.idris}s.
`Postgres.Typed.Operations.create`{.idris} does the trick, so in any `HasIO`{.idris} context, we can:
```idris
withConnection "user=pgidr_role dbname=pgidr_db" $ \conn => do
  result <- runMonadExec (create conn Person)
```
Here, `runMonadExec`{.idris} executes an operation (that is, a `MonadExec`{.idris} action),
and it is responsible for error reporting, among other things.
The `result`{.idris} of `runMonadExec action`{.idris} is a `Either ExecError res`{.idris},
where `res`{.idris} is the original result of the action (a `()`{.idris} in this particular case).

### Inserting records

Then, we can insert a few records into our DB:
```idris
  result <- execute' conn (insert into Person [ Nothing, "John", "Doe", 42 ])
```
Here, `execute'`{.idris} is another shortcut for executing `MonadExec`{.idris} actions.
The `result`{.idris} here is also `Either ExecError ()`{.idris},
since a plain `INSERT`{.sql} query doesn't return anything.

We can ask it to return the primary key of the record we just inserted, though:
```idris
  result <- execute' conn (insert' into Person [ Nothing, "John", "Doe", 42 ] { returning := column "id" })
```
and `result`{.idris} here is an `Either ExecError Integer`{.idris}.
We can ask for more than one column:
```idris
  result <- execute' conn (insert' into Person [ Nothing, "John", "Doe", 42 ] { returning := columns ["id", "first_name"] })
```
or even the whole row:
```idris
  result <- execute' conn (insert' into Person [ Nothing, "John", "Doe", 22 ] { returning := all })
```
The types of the corresponding `result`{.idris}s will be just as you'd expect!

## Building

Assuming you have [pack](https://github.com/stefan-hoeck/idris2-pack) and PostgreSQL libraries installed,
```shell
pack build pgidr.ipkg
```
should do.

## Package structure

The most important modules are:

* `Postgres.C.Connection` — all things connection: establishing the connection, querying its status, and so on.
* `Postgres.C.Query` — making queries (via a previously established connection).

## Caveats and compromises

### Typed pq functions

Certain PostgreSQL API functions (in particular `PQexecParams` and `PQprepare`)
allow passing the (PostgreSQL) types of the query parameters.
When the types are missing, the server derives those from the context.

We've chosen to _not_ expose these types in the API,
as the added clumsiness and complexity doesn't seem to be justified by the benefits.
Please let us know if your use case requires
explicit passing of the types to the PostgreSQL server.
