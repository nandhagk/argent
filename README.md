# Argent

Argent works out how many steps your Rocq functions take, and helps you prove bounds on them.

You write plain Gallina. The command `TimeFun f` reads the definition of `f` and defines a new
function `T_f`, which takes the same arguments as `f` (plus a time function for each function
argument) and returns the number of steps that `f` takes, one step per function call. You then
prove bounds on `T_f` by induction, as you would for any other function, and you can state them
in big-O notation. Your code carries no cost annotations, and its extracted OCaml is unchanged.

## A first example

This example comes from [`examples/Lists.v`](examples/Lists.v), which starts with these
imports. Times are binary numbers of type `N`, so the file opens `N_scope`.

```coq
From Stdlib Require Import NArith Lia.
From Stdlib Require List.
From Argent Require Import Time Tactics Complexity Std.
Import List.ListNotations ComplexityNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
```

Here is an ordinary function:

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

`Print T_append` shows what `TimeFun` derived:

```text
T_append =
fix T_append (A : Type) (l1 l2 : list A) {struct l1} : N :=
  (1 + match l1 with
       | [] => 0
       | _ :: r => T_append A r l2
       end)%N
```

It has the same shape as `append`, and `A` is implicit as in `append`, so you write
`T_append l1 l2`. Every call costs 1, and the call on `x :: r` also pays for the recursive call
on `r`. So `append l1 l2` takes one step per element of `l1`, plus one. The example file states
the two cases of `T_append` as lemmas, `T_append_nil : T_append [] l2 = 1` and
`T_append_cons : T_append (x :: r) l2 = 1 + T_append r l2`, each proved by `reflexivity`. With
them, the proof is an induction:

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

For a bound stated with `<=`, the tactic `time_step` does these steps itself, so most bounds
take one line:

```coq
Theorem T_append_le {A : Type} (l1 l2 : list A) :
  T_append l1 l2 <= N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH]; time_step.
Qed.
```

In big-O notation, a weaker form of the same result reads:

```coq
Theorem append_complexity {A : Type} :
  T_append (A := A) l1 l2 ∈ 𝑂(N.of_nat (length l1)) for (l1, l2).
```

`for (l1, l2)` names the arguments that the bound ranges over. The tutorial explains the rest
of the notation.

## Examples, in reading order

| File | What it shows |
| --- | --- |
| [`examples/Lists.v`](examples/Lists.v) | Reading a time function; proving a bound by hand and with `time_step`; big-O statements; a quadratic against a linear algorithm; functions passed as arguments |
| [`examples/Trie.v`](examples/Trie.v) | Bounds in the bit length of a number, a lower bound, and Θ in the worst case |
| [`examples/Queue.v`](examples/Queue.v) | An amortised bound, proved with a potential |
| [`examples/KeyedMap.v`](examples/KeyedMap.v) | Signatures that carry time bounds, and a client functor that relies on those bounds alone |
| [`examples/Loops.v`](examples/Loops.v) | Loops over an accessibility proof and over fuel |
| [`examples/Halving.v`](examples/Halving.v) | Well-founded recursion with `Fix` |

[`docs/tutorial.md`](docs/tutorial.md) walks through them in this order.

## What's in the library

The theories live under the logical name `Argent`.

| Theory | What you use it for |
| --- | --- |
| `Time` | The commands. `TimeFun` derives time functions; `TimeCheck`, `TimeAudit`, `TimePrim`, `TimePrimTable`, `TimeUnfold` and `TimeBound` check or adjust them. Also the tactic `time_unfold`. |
| `Tactics` | Proving bounds: `time_step`, `time_simpl`, `time_cbn`, `time_pose`, `time_lin`, `loop_bound` and `amortise`. |
| `Std` | Time functions and bounds for the standard library's functions on lists, booleans, pairs, `nat`, `positive`, `N` and `Z`, and for `Fix` and the other well-founded recursors. |
| `Complexity` | 𝑂, Ω, Θ, worst-case and amortised bounds, their lemmas, and the notation `T ∈ 𝑂(g) for x`. |
| `Amortised` | The potential method for sequences of operations. |
| `Loop` | Two loop combinators, `loop` and `loop_fuel`, whose bounds come from a potential. |

## Building

The flake pins Rocq 9.3.0, its standard library and rocq-elpi 3.5.0. In the flake's
development shell, `just build` builds the library and the examples. `just test` first checks
that no source file admits a proof or declares an axiom, then builds the tests.

```sh
nix develop
just build
just test
```

Another flake can depend on Argent through `packages.default`, which installs the theories.

## Where to go next

- [`docs/tutorial.md`](docs/tutorial.md) teaches the library step by step, through the
  examples.
- [`docs/reference.md`](docs/reference.md) describes the cost model and every command, tactic,
  bound and error code.
- [`docs/design.md`](docs/design.md) explains how the translation works, why its costs match the
  extracted program, and what the design leaves out.

## Licence

Argent is released under the MIT licence. See [`LICENSE`](LICENSE).
