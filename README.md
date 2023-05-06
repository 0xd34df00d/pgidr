**pgidr** — PostgreSQL bindings for Idris

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
