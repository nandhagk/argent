# Argent manual

Argent derives a time function `T_f` from the body of a Gallina definition `f`, and provides
the lemmas and tactics to prove big-O bounds on it, including amortised ones. Programs stay
plain Gallina, and no cost annotation appears in the code. This manual describes the cost
model, the commands, the tactics, the convention for signatures, the recipe for amortised
bounds and the limits of the library.

## Cost model

`T_f a₁ … aₙ` is the number of steps that the call `f a₁ … aₙ` takes under call-by-value
evaluation of the extracted program. One step is one call of a defined function or of a closure
body. `T_f` adds 1 for the call of `f` itself, adds the costs of evaluating the arguments of
every call in the body, and adds the time functions of the callees. A `match` costs its
scrutinee plus the branch that runs, and a `let` costs its value once. Types and proofs are
erased, so they cost nothing. A constant applied only to types and proofs, such as `@nil A`,
is evaluated once when the program starts, so it also costs nothing.

A function argument `g` of `f` gets a companion `T_g` right after it in `T_f`. For example,
`T_map` has the type `forall A B, (A -> B) -> (A -> nat) -> list A -> nat`. At a call site
the companion is derived from the argument itself. A closure `fun x => e` has the companion
`fun x => 1 + T⟦e⟧`, and a partial application `h a` has `fun x => T_h a x`, whose argument
`a` is paid once, when the closure is created. Function values may be passed as arguments,
but they may not be stored in data, because a closure taken out of data has no companion.

The model counts steps up to a constant factor that depends only on the program text. A body
contains no loop other than calls, so the work between two counted calls is bounded by the
size of the largest body. Numbers in `nat`, `positive`, `N` and `Z` are the inductive types of
the standard library, so `nat` arithmetic is unary and binary arithmetic costs one step per
bit. A cost that extraction realises natively must be declared with `TimePrim`.

## Commands

All commands are in `Argent.Time`, so a file that derives time functions starts with
`From Argent Require Import Time.`

`TimeFun f g …` derives `T_f`, `T_g`, … and places each beside its constant. For a mutual
block, it derives a time function for every member that is a constant, as one mutual fixpoint.
For a constant of another library, it must run in a module named like the last component of the
constant's path, so that `Nat.add` gets `Nat.T_add`. Library modules already provide these
for the standard library (see `Argent.Std`).

```coq
Fixpoint size (t : tree) : nat :=
  match t with
  | Node _ ts => 1 + fold_right Nat.add 0 (map size ts)
  end.

TimeFun size.
```

`TimeFun` charges a call of `g` with the time function of `g`. It takes the one that an earlier
`TimeFun` recorded, or else the constant `T_g` beside `g`, which is how it finds the time
functions of functor parameters and functor instances. When that `T_g` has a body, `TimeFun`
derives the time function of `g` again and fails with `E_CHECK` when the result is not
convertible with `T_g`. Deriving it again checks the callees of `g` in the same way, so a
hand-written time function is caught at any depth. A `T_g` without a body, such as a `Parameter`
of a module type, is used as it is. Each check runs once per command, and its result is
recorded for later commands, until the end of the enclosing functor when there is one. A
constant whose body is another constant, as in the module alias `Module K := K0.`, is charged
with the time function of that constant, because extraction defines it as that constant.

`TimeCheck f …` derives the time function of `f` again and fails when it is not convertible
with the stored `T_f`. A time function therefore cannot be edited by hand.

```coq
TimeCheck size.
```

`TimeAudit r …` walks every constant that the roots `r` call, transitively, runs `TimeCheck` on
each, and fails on a computational constant that has neither a time function nor a `TimePrim`
cost. Run it on the roots that you extract.

```coq
TimeAudit Trie.get Trie.set Queue.step.
```

`TimePrim c := (e)` declares the cost `e` of a constant that has no usable body, such as an
opaque constant or one that extraction replaces by native code. The type of `e` is the time
type of `c`. `TimePrim c := n` declares a constant cost `n`. It is the only way to write a cost
by hand, so its uses are the place to review.

```coq
TimePrim opaque_double := (fun n => n + 1).
```

`TimeUnfold c …` makes the translation unfold `c` at every call before translating it. A
beta-redex `(fun x => k) m` is charged as `let x := m in k`. Code written in an identity monad
therefore costs what the same code written with `let` costs.

```coq
Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B := f m.
TimeUnfold ret bind.
```

`TimeBound L` registers a lemma `L : forall x̄, [P x̄ ->] T_g ā <= B` for `time_pose`. A lemma
named `T_g_le` beside `T_g` is found without registration, which is the only way inside a
functor, because Elpi databases cannot be extended there.

```coq
Lemma twice_bound (n : nat) : T_twice n <= n + 2.
TimeBound twice_bound.
```

`TimeFunFails "E_CODE" f` succeeds when `TimeFun f` fails with the error code `E_CODE`, and
declares nothing. It is meant for tests.

`TimeFun` rejects a definition whose cost it cannot account for. Each rejection has its own
code.

| Code | Cause |
| --- | --- |
| `E_CLOSURE_DATA` | A function value is stored in a constructor or passed where a polymorphic callee expects data. |
| `E_CLOSURE` | A function value appears where data is expected. |
| `E_NO_TIME` | A called function has no time function, including a closure taken out of data. |
| `E_OVERAPP` | A call has more arguments than the callee's type has binders, for example a call of the result of a polymorphic function. |
| `E_MATCH_FN` | A `match` returns a function. Eta-expand the match. |
| `E_WF` | The definition uses well-founded recursion through `Fix`, `Fix_F` or `Acc_rect`. Use `loop` or `loop_fuel`. |
| `E_OPAQUE` | The constant, or a callee, is opaque or has no body. |
| `E_SECTION` | The definition uses a section variable. Run `TimeFun` after the section closes, or make the variable a functor parameter. |
| `E_TERM` | The term has a form that the translation does not support. |
| `E_CHECK` | The time function found beside a callee is not the one derived from the callee's body. |
| `E_NOT_CODE`, `E_PLACE`, `E_TIMED` | The command targets a type or proof, runs in the wrong module, or repeats an earlier derivation. |

## Tactics

The tactics are in `Argent.Tactics`. Time functions never unfold under `cbn` or `simpl`, so a
plain `cbn` computes the specification functions in a goal and leaves every time function
folded.

- `time_unfold T_f` unfolds by one step every application of `T_f` whose structural argument is
  a constructor, and refolds its recursive calls.
- `time_simpl` replaces the time functions whose value is a numeral, such as `T_negb`, by that
  numeral.
- `time_pose` adds, for each time function applied in the goal, its registered bound, its
  sibling `T_g_le` and the matching quantified hypotheses, such as an induction hypothesis or a
  bound on a companion. It discharges premises with `assumption`, `lia` or
  `eauto with time_inv`.
- `time_step` unfolds the time function on the left of a goal `T_f ā <= e` by one step, runs
  `time_simpl` and `cbn`, poses the bounds, and tries `nia`. When `nia` fails, it destructs the
  scrutinees of the matches left in the goal and tries again. `time_step f` names the function
  `f` instead.
- `loop_bound Inv Phi Tstop` applies the potential lemma of `loop` or `loop_fuel`.
- `amortise Inv Phi A k` applies `amortised_uniform`.

Most per-operation bounds take one line.

```coq
Theorem T_get_le {A : Type} (p : positive) (m : t A) : T_get p m <= Pos.size_nat p.
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.
```

## Big-O statements

`bigO P g T` says that `T x <= c * (g x + 1)` for some constant `c` and every input `x` that
satisfies `P`. The input is the tuple of all arguments, so the constant does not depend on any
of them. `tight P g T` adds a lower bound, which holds on inputs of every size. `bigO_intro`,
`bigO_le`, `bigO_mono`, `bigO_add`, `bigO_trans`, `bigO_comp` and `tight_intro` build such
statements from bounds with explicit constants. State the per-operation lemmas with explicit
constants, and publish the `bigO` corollaries.

## Signatures

A module type that describes an operation has two layers. The functional layer declares the
operation and its laws. The time layer declares the time function, a named constant and a
contract that bounds the time function by that constant.

```coq
Module Type MAP.
  Declare Module K : KEY.
  Parameter t : Type -> Type.
  Parameter get : forall {A : Type}, K.t -> t A -> option A.
  Parameter get_set_same : forall A k (v : A) m, get k (set k v m) = Some v.
  (* Time layer. *)
  Parameter T_get : forall {A : Type}, K.t -> t A -> nat.
  Parameter c_map : nat.
  Parameter T_get_le :
    forall A k (m : t A), T_get k m <= c_map * (Pos.size_nat (K.encode k) + 1).
End MAP.
```

An implementation defines the operation, runs `TimeFun` on it, which derives `T_get`, and proves
`T_get_le` for its own value of `c_map`. A client is a functor over the signature. Its own
`TimeFun` calls `M.T_get` through the sibling rule, and its bounds can use only the contracts,
so they hold for every implementation. The contracts are `Parameter`s of the module type, so
they add no axiom. Every instance must prove them.

## Amortised bounds

An amortised bound follows the potential method. The following steps give it for a data
structure.

1. Define the operations as one function `step : op -> S -> S` over an inductive type `op` of
   operations, and run `TimeFun step`.
2. Choose a potential `Phi : S -> nat`, an invariant `Inv`, and an amortised cost `A o s`.
3. Prove `amortised step T_step A Phi Inv`, which says that every operation keeps `Inv` and
   that `T_step o s + Phi (step o s) <= A o s + Phi s`.
4. Apply `amortised_run` for the exact statement, or `amortised_uniform`, through the tactic
   `amortise`, for the bound `total step T_step os s <= k * length os + Phi s`.

The bound holds along one sequence of versions. It says nothing about a history in which one
version is used twice, because repeating an expensive operation on the same version is not
paid for. A loop is bounded the same way. Its potential must strictly decrease by the cost of
each step, because each iteration also costs one call.

## Limits

- The translator is trusted. It is an unverified Elpi program, and `TimeCheck` checks only that
  a stored time function is what the translator produces.
- `cofix` cannot be translated, because rocq-elpi does not read cofixpoints.
- Well-founded recursion by `Fix`, `Program Fixpoint`, `Function` or Equations is rejected.
  Use `loop` over an accessibility proof or `loop_fuel`.
- Closures cannot be stored in data. A record of functions becomes a functor parameter.
- A definition whose body returns a function, such as `Pos.compare := Pos.compare_cont Eq`, is
  eta-expanded, so its partial applications pay the cost of creating the closure at every call.
  This overestimates the cost of a reused partial application by a constant per call.
- A closure that a beta-redex or `TimeUnfold` substitutes is not charged the 1 of its call. A
  let-bound closure is charged it. Both are within the constant factor of the model.
- `TimeAudit` does not compare the `TimePrim` table with the constants that extraction realises
  natively.
- Database facts that a command records inside a functor are dropped when the functor ends.
  So `TimePrim`, `TimeUnfold`, `TimeBound` and `TimeFun` for a constant of another library
  belong outside functors. rocq-elpi gives no way to tell that a command runs inside a functor,
  so these commands cannot reject it there. The message of `E_NO_TIME` and of `E_OPAQUE` for a
  callee names this cause, and a bound registered inside a functor is simply not posed.
