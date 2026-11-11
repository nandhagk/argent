set shell := ["bash", "-euo", "pipefail", "-c"]
set positional-arguments

# List the recipes.
[default]
help:
    @just --list

# Build the library and the examples; arguments go to dune.
build *args:
    dune build theories examples "$@"

# Build the tests after the source check; arguments go to dune.
test *args: check
    dune build tests "$@"

# Fail when a source admits a proof or declares an axiom.
check:
    ! git grep -nE 'Admitted|admit\.|Axiom|give_up' -- theories tests examples

# Remove the build outputs.
clean:
    dune clean
