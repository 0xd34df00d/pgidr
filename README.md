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
