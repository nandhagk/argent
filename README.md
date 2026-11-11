# Argent

Argent is a Rocq library that derives time functions from plain Gallina definitions and proves
big-O bounds on them, including amortised bounds. A command, written in rocq-elpi, reads the
kernel body of a definition `f` and defines `T_f`, the number of steps of call-by-value
evaluation of `f` on its arguments. Programs contain no cost annotation, and their extracted
code is unchanged.

```coq
From Argent Require Import Time Tactics Std.

Fixpoint get {A : Type} (p : positive) (m : t A) {struct p} : option A :=
  match m with
  | Leaf => None
  | Node l v r =>
    match p with
    | xH => v
    | xO q => get q l
    | xI q => get q r
    end
  end.

TimeFun get.

Theorem T_get_le {A : Type} (p : positive) (m : t A) : T_get p m <= Pos.size_nat p.
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.
```

## Contents

The library has the following theories, under the logical name `Argent`.

- `Time` holds the translator and the commands `TimeFun`, `TimeCheck`, `TimeAudit`,
  `TimePrim`, `TimePrimTable`, `TimeUnfold` and `TimeBound`.
- `BigO` defines `bigO` and `tight` with their closure lemmas.
- `Amortised` proves the potential method for sequences of operations.
- `Loop` defines a loop over an accessibility proof and a loop with fuel, each with a potential
  lemma that bounds its time independently of the proof and the fuel.
- `Std` derives the time functions of the standard-library functions on lists, booleans, pairs,
  `nat`, `positive`, `N` and `Z`, with a bound for each of the common ones, including division,
  gcd, shifts and the bitwise operations on `Z`. It also derives the time functions of the
  well-founded recursors `Fix_F`, `Fix`, `Acc_rect` and `well_founded_induction_type`, with a
  potential lemma for each.
- `Tactics` holds `time_pose`, `time_simpl`, `time_step`, `loop_bound` and `amortise`.

The directory `examples` (`Argent.Examples`) holds a binary trie with a tight bound, a two-list
queue with an amortised bound, maps over abstract keys with a client functor that uses only the
signature's contracts, two loops, and two functions defined by `Fix` and bounded through the
potential lemma of `Fix`. The directory `tests` (`Argent.Tests`) checks every feature of the command,
every rejection, the tactics, the bounds of `Std`, the assumptions of the example theorems and
the extraction of the loop and of a function defined by `Fix`.

`docs/manual.md` explains how to use the library, and `docs/design.md` records the design, the
translation rules and their meta-theory.

## Building

The flake pins Rocq 9.3, its standard library and rocq-elpi 3.5.0. Inside its development shell,
`just build` builds the library and the examples, and `just test` builds the tests after
checking that no source admits a proof or declares an axiom.

```sh
nix develop
just build
just test
```

Another flake can depend on the library through `packages.default`, which installs the theory
`Argent`.

## Licence

Argent is released under the MIT licence. See `LICENSE`.
