# Argent

Time functions for Rocq programs, derived from their definitions, and big-O bounds on them.

- `TimeFun f` reads the body of `f` and defines `T_f`.
- `T_f` takes the arguments of `f`, plus a time function for each function argument.
- `T_f` returns the number of steps that `f` takes: one per function call.
- Bounds on `T_f` are ordinary theorems, proved by induction or with the tactic `time_step`.
- Programs carry no cost annotations. Their extracted OCaml is unchanged.

## Example

From [`examples/Lists.v`](examples/Lists.v). The file starts with:

```coq
From Stdlib Require Import NArith Lia.
From Stdlib Require List.
From Argent Require Import Time Tactics Complexity Std.
Import List.ListNotations ComplexityNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
```

Times have type `N`, hence `N_scope`.

A function, and the command that derives its time function:

```coq
Fixpoint append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: r => x :: append r l2
  end.
```

```coq
TimeFun append.
```

`Print T_append`:

```text
T_append =
fix T_append (A : Type) (l1 l2 : list A) {struct l1} : N :=
  (1 + match l1 with
       | [] => 0
       | _ :: r => T_append A r l2
       end)%N
```

- `1 +`: one step for the call of `append`.
- `match`: kept, because the cost depends on the branch taken.
- `T_append A r l2`: the recursive call.
- `l2` and `x ::` cost nothing: variables and constructors are free.
- `A` is implicit, as in `append`.

The exact cost, by induction. `T_append_nil` and `T_append_cons` are the two cases of
`T_append`, stated in the file and proved by `reflexivity`.

```coq
Theorem T_append_exact {A : Type} (l1 l2 : list A) :
  T_append l1 l2 = N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH].
  - rewrite T_append_nil. reflexivity.
  - (* T_append (x :: r) l2 is 1 + T_append r l2, and the IH gives T_append r l2. *)
    rewrite T_append_cons, IH. cbn [length]. lia.
Qed.
```

An upper bound in one line. `time_step` proves goals of the form `T_f args <= bound`.

```coq
Theorem T_append_le {A : Type} (l1 l2 : list A) :
  T_append l1 l2 <= N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH]; time_step.
Qed.
```

A weaker form in big-O notation. `for (l1, l2)` names the arguments that the bound ranges over.

```coq
Theorem append_complexity {A : Type} :
  T_append (A := A) l1 l2 ∈ 𝑂(N.of_nat (length l1)) for (l1, l2).
```

## Examples

In reading order:

| File | Topic |
| --- | --- |
| [`examples/Lists.v`](examples/Lists.v) | Reading a time function; bounds by hand and with `time_step`; big-O; a quadratic and a linear algorithm; functions as arguments |
| [`examples/Trie.v`](examples/Trie.v) | Bounds in the bit length of a number; a lower bound; Θ in the worst case |
| [`examples/Queue.v`](examples/Queue.v) | An amortised bound, proved with a potential |
| [`examples/KeyedMap.v`](examples/KeyedMap.v) | Signatures with time bounds; a client functor that relies on those bounds alone |
| [`examples/Loops.v`](examples/Loops.v) | Loops over an accessibility proof and over fuel |
| [`examples/Halving.v`](examples/Halving.v) | Well-founded recursion with `Fix` |

## Library

Logical name `Argent`.

| Theory | Contents |
| --- | --- |
| `Time` | The commands `TimeFun`, `TimeCheck`, `TimeAudit`, `TimePrim`, `TimePrimTable`, `TimeUnfold` and `TimeBound`; the tactic `time_unfold` |
| `Tactics` | `time_step`, `time_simpl`, `time_cbn`, `time_pose`, `time_lin`, `loop_bound`, `amortise` |
| `Std` | Time functions and bounds for the standard library: lists, booleans, pairs, `nat`, `positive`, `N`, `Z`, `Fix` and the other well-founded recursors |
| `Complexity` | 𝑂, Ω, Θ, worst-case and amortised bounds; their lemmas; the notation `T ∈ 𝑂(g) for x` |
| `Amortised` | The potential method for sequences of operations |
| `Loop` | The loops `loop` and `loop_fuel`, with bounds from a potential |

## Building

```sh
nix develop
just build
just test
```

- The flake pins Rocq 9.3.0, its standard library and rocq-elpi 3.5.0.
- `just build` builds the library and the examples.
- `just test` checks that no source admits a proof or declares an axiom, then builds the tests.
- Other flakes can depend on `packages.default`, which installs the theories.

## Documentation

- [`docs/tutorial.md`](docs/tutorial.md): the library step by step, through the examples.
- [`docs/reference.md`](docs/reference.md): cost model, commands, tactics, bounds, error codes.
- [`docs/design.md`](docs/design.md): how the translation works, why its costs match the
  extracted program, and the limits of the design.

## Licence

MIT. See [`LICENSE`](LICENSE).
