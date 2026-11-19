# Argent tutorial

- Covers: deriving time functions, proving bounds on them, stating complexities, amortised bounds, loops and well-founded recursion.
- Prerequisites: inductive types, `Fixpoint`, proofs by induction, `lia`. Steps 8 to 10 also use modules and functors, `sig` types, dependent `match` and accessibility proofs (`Acc`).
- Each step uses one file in [`examples/`](../examples). Steps 1 to 5 use [`examples/Lists.v`](../examples/Lists.v).

## 1. A first time function

The header of `examples/Lists.v`:

```coq
From Stdlib Require Import NArith Lia.
From Stdlib Require List.
From Argent Require Import Time Tactics Complexity Std.
Import List.ListNotations ComplexityNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
```

- `Time`: the command `TimeFun`.
- `Tactics`: tactics for bounds.
- `Complexity`: the big-O notation of step 3.
- `Std`: time functions of the standard library, such as `Nat.T_add` for addition on `nat`.
- Times have type `N`, hence `N_scope`. A sum of `nat`s is marked `%nat`.

A function:

```coq
Fixpoint append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: r => x :: append r l2
  end.
```

Its time function:

```coq
TimeFun append.
```

`TimeFun append` defines `T_append` next to `append`. `T_append l1 l2` is the number of steps of `append l1 l2`. `Print T_append` shows:

```text
T_append =
fix T_append (A : Type) (l1 l2 : list A) {struct l1} : N :=
  (1 + match l1 with
       | [] => 0
       | _ :: r => T_append A r l2
       end)%N
```

- Same shape as `append`, with costs in place of values.
- `1 +`: one step for the call of `append`.
- `match`: kept, because the cost depends on the branch taken.
- `l2`: variables and constructors cost nothing.
- `append r l2` costs `T_append r l2`. The constructor `x ::` adds nothing.
- `A` is implicit, as in `append`: write `T_append l1 l2`.

The cost model ([all rules](reference.md#cost-model)):

- A call is charged with the time function of the function it calls.
- Every time function starts with `1 +` for its own call.
- Types and proofs cost nothing, because extraction erases them.

Times are binary numbers, so time functions evaluate fast:

```coq
Example T_append_three : T_append [1; 2; 3] [4; 5] = 4 := eq_refl.
```

Four calls: on `[1; 2; 3]`, `[2; 3]`, `[3]` and `[]`.

The two cases of `T_append` as equations. `TimeFun` doesn't generate these: they are stated by hand and proved by `reflexivity`, since they hold by computation.

```coq
Lemma T_append_nil {A : Type} (l2 : list A) : T_append [] l2 = 1.
Proof.
  reflexivity.
Qed.

Lemma T_append_cons {A : Type} (x : A) (r l2 : list A) :
  T_append (x :: r) l2 = 1 + T_append r l2.
Proof.
  reflexivity.
Qed.
```

## 2. Proving a bound

By induction, with the case equations:

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

- `length` returns a `nat` and times are `N`. A size enters a bound as `N.of_nat` of the size.
- `lia` reasons through `N.of_nat`.
- Most bounds take three moves: unfold the time function once, use the induction hypothesis or a bound on a callee, finish the arithmetic.

`time_step` makes these moves on a goal `T_f args <= bound`:

- It unfolds `T_f` once.
- It adds the known bounds of the other time functions in the goal. A bound on `T_g` is known when a lemma named `T_g_le` sits next to `T_g`, or when it was registered with `TimeBound`. `Argent.Std` has such lemmas for the standard library.
- It finishes with `lia` or `nia`, which use the hypotheses in context, such as the induction hypothesis.

```coq
Theorem T_append_le {A : Type} (l1 l2 : list A) :
  T_append l1 l2 <= N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH]; time_step.
Qed.
```

`time_step` proves only `<=` goals. An exact cost needs a proof by hand.

## 3. Stating the complexity

```coq
Theorem append_complexity {A : Type} :
  T_append (A := A) l1 l2 ∈ 𝑂(N.of_nat (length l1)) for (l1, l2).
Proof.
  apply bigO_intro with (c := 1). intros [l1 l2] _. rewrite T_append_exact. lia.
Qed.
```

- Reading: `T_append l1 l2` is in 𝑂 of the length of `l1`, over all pairs `(l1, l2)`.
- Meaning: one constant `c` such that `T_append l1 l2 <= c * (N.of_nat (length l1) + 1)` for every input. The `+ 1` allows a constant cost at size 0.
- Proof: `bigO_intro` takes the constant and leaves `forall x, P x -> T x <= c * g x + c`. Here `x` is the pair `(l1, l2)`, and `P x` is `True`, which `_` discards.

Notation details:

- `for (l1, l2)` names the arguments. A pattern can't carry types, so `(A := A)` fixes the implicit argument of `T_append`.
- A precondition goes after a bar: `for x | P x`. Without one, the bound covers every input.
- `𝑂` is U+1D442 (mathematical italic capital O), a different character from the constructor `O` of `nat`. Copy it from an example if the editor can't type it.
- The notation comes from `ComplexityNotations`, which the header of step 1 imports.
- Other bounds: Ω, Θ, the worst case, amortised. Step 6 uses the worst case. [The reference](reference.md#complexity-bounds) lists them all.

## 4. Comparing two algorithms

`slow_rev` appends each element after the reversed rest:

```coq
Fixpoint slow_rev {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: r => append (slow_rev r) [x]
  end.
```

The call of `append` is charged with `T_append`, applied to the arguments that `append` receives. The example file states this case as a lemma, proved by `reflexivity`:

```coq
Lemma T_slow_rev_cons {A : Type} (x : A) (r : list A) :
  T_slow_rev (x :: r) = 1 + (T_slow_rev r + T_append (slow_rev r) [x]).
```

- `T_append (slow_rev r) [x]` grows with the length of `r`, so the total is quadratic.
- The proof also needs a fact about values: reversing keeps the length.

```coq
Lemma length_slow_rev {A : Type} (l : list A) : length (slow_rev l) = length l.
```

```coq
Theorem T_slow_rev_le {A : Type} (l : list A) :
  T_slow_rev l <= (N.of_nat (length l) + 1) * (N.of_nat (length l) + 1).
Proof.
  induction l as [| x r IH].
  - (* Both sides compute to 1, and [reflexivity] also proves [1 <= 1]. *)
    reflexivity.
  - (* The append costs length r + 1, by T_append_exact. *)
    rewrite T_slow_rev_cons, T_append_exact, length_slow_rev. cbn [length]. lia.
Qed.
```

`rev_onto` moves the elements onto an accumulator and calls nothing else, so it is linear:

```coq
Fixpoint rev_onto {A : Type} (l acc : list A) : list A :=
  match l with
  | [] => acc
  | x :: r => rev_onto r (x :: acc)
  end.
```

- `time_unfold @T_rev_onto` unfolds `T_rev_onto` once, without an equation lemma.
- The `@` passes the constant itself, without filling in its implicit argument.

```coq
Theorem T_rev_onto_exact {A : Type} (l acc : list A) :
  T_rev_onto l acc = N.of_nat (length l) + 1.
Proof.
  revert acc. induction l as [| x r IH]; intros acc.
  - reflexivity.
  - time_unfold @T_rev_onto. rewrite IH. cbn [length]. lia.
Qed.
```

Time functions never unfold under `cbn` or `simpl`. Unfold them with `time_unfold`, `time_step` or an equation lemma.

## 5. Functions as arguments

The cost of `map f l` depends on the cost of `f`:

```coq
Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: r => f x :: map f r
  end.
```

`T_map` takes one more argument, right after `f`: a time function for `f`, called its *companion*.

```text
T_map : forall {A B : Type}, (A -> B) -> (A -> N) -> list A -> N
T_map f T_f (x :: r) = 1 + (T_f x + T_map f T_f r)
```

A bound on `T_map` assumes a bound on the companion:

```coq
Theorem T_map_le {A B : Type} (f : A -> B) (T_f : A -> N) (k : N) (l : list A) :
  (forall x, T_f x <= k) -> T_map f T_f l <= (k + 1) * N.of_nat (length l) + 1.
```

Companions never appear in programs. At each call of `map`, `TimeFun` derives the companion from the argument:

- A closure `fun m => e` gets `fun m => 1 + (the cost of e)`.
- A named function `g` gets its time function `T_g`.

```coq
Definition add_to_all (n : nat) (l : list nat) : list nat := map (fun m => (n + m)%nat) l.
```

What `TimeFun add_to_all` derives, stated in the example file as a lemma proved by `reflexivity`:

```coq
Lemma T_add_to_all_eq (n : nat) (l : list nat) :
  T_add_to_all n l = 1 + T_map (fun m => (n + m)%nat) (fun m => 1 + Nat.T_add n m) l.
```

- Addition on `nat` recurses on its first argument, so `Nat.T_add n m <= n + 1` (`Nat.T_add_le` in `Argent.Std`).
- To bound `T_add_to_all`: bound one call of the closure, then apply `T_map_le`.

```coq
Theorem T_add_to_all_le (n : nat) (l : list nat) :
  T_add_to_all n l <= (N.of_nat n + 3) * N.of_nat (length l) + 2.
Proof.
  rewrite T_add_to_all_eq.
  assert (Hcall : forall m, 1 + Nat.T_add n m <= N.of_nat n + 2).
  { intros m. pose proof (Nat.T_add_le n m). lia. }
  pose proof (T_map_le (fun m => (n + m)%nat) (fun m => 1 + Nat.T_add n m) (N.of_nat n + 2) l
    Hcall) as Hmap.
  lia.
Qed.
```

- Functions can be passed as arguments.
- Functions can't be stored in data: a closure taken out of a list or a record has no companion. `TimeFun` rejects such code with `E_CLOSURE_DATA`. Step 8 shows the alternative.

## 6. Numbers and lower bounds

[`examples/Trie.v`](../examples/Trie.v) stores values in a binary trie under keys of type `positive`. `get` reads the key one bit at a time, so its cost depends on the bit length of the key, `Pos.size_nat p`:

```text
T_get =
fix T_get (A : Type) (p : positive) (m : t A) {struct p} : N :=
  (1 +
   match m with
   | Leaf => 0
   | Node l _ r =>
       match p with
       | q~1%positive => T_get A q r
       | q~0%positive => T_get A q l
       | 1%positive => 0
       end
   end)%N
```

The upper bound is routine, so `time_step` proves it. The induction runs on the key, for every trie:

```coq
Theorem T_get_le {A : Type} (p : positive) (m : t A) :
  T_get p m <= N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.
```

- A lookup that misses can stop at the first leaf, so no lower bound in the bit length holds on every input.
- On a trie that holds the key, `get` reads every bit (`T_get_ge`).
- `Θ_worst` combines both: the upper bound on every input, and the lower bound on some input of every size.

```coq
Theorem get_worst_complexity {A : Type} (a : A) :
  T_get (A := A) p m ∈ Θ_worst(N.of_nat (Pos.size_nat p)) for (p, m).
```

- The proof, by `tight_intro`, names those slow inputs: the key `ones n`, with `n` ones after its leading 1, in a trie that holds it.
- Building that trie needs a value to store, hence the argument `a : A`.

Numbers in this model:

- `positive`, `N` and `Z` are inductive types, and their arithmetic costs what its Gallina code costs.
- Each recursive call handles one bit. Addition is linear in the number of bits; multiplication and division are quadratic (see the bounds in `Argent.Std`).
- `nat` arithmetic is unary.
- For numbers extracted to native integers, see [`TimePrim`](reference.md#timeprim).

## 7. Amortised bounds

[`examples/Queue.v`](../examples/Queue.v) is a queue made of two lists. `push` adds to the back list, and `pop` takes from the front list. When the front is empty, `pop` first reverses the back list into the front:

```text
T_pop =
fun (A : Type) (q : queue A) =>
(1 +
 (let (f, b) := q in
  match f with
  | [] => List.T_rev_append b []
  | _ :: _ => 0
  end))%N
```

- One `pop` can take time linear in the size of the queue.
- Each element is reversed at most once, so a sequence of operations costs a constant per operation.
- The potential method proves this. A potential is a number attached to each state, here the length of the back list:

```coq
Definition back_length {A : Type} (q : queue A) : N := N.of_nat (length (snd q)).
```

Each operation, plus the potential it creates, minus the potential it uses up, costs at most a constant:

- `push`: costs 2 and raises the potential by 1, which makes 3.
- `pop` that reverses `b`: costs `length b + 3` and lowers the potential by `length b`, which makes 3.
- Any other `pop`: costs 2.
- The example states the bound 4, which also holds.

The operations go behind one function, `step`. The property is called `amortised`:

```coq
Theorem step_amortised {A : Type} :
  amortised (@step A) T_step (fun _ _ => 4%N) back_length (fun _ => True).
```

- The last argument is an invariant that every operation keeps, here `True`.
- Summing over a sequence gives the bound. The tactic `amortise` applies the summing lemma and leaves four small goals, each commented in the file.

```coq
Theorem queue_total {A : Type} (os : list (op A)) :
  (total (@step A) T_step os empty <= 4 * N.of_nat (length os))%N.
```

The bound holds along one sequence, where each operation works on the queue that the previous one returned. It says nothing about using an old queue twice: an expensive `pop` repeated on the same queue is never paid for.

## 8. Generic code

[`examples/KeyedMap.v`](../examples/KeyedMap.v) has code that is generic over a module.

- Generic code can't look inside its parameter. Its bounds come from the parameter's signature.
- So a signature has a *time layer* next to its operations and laws: a time function for each operation, a named constant, and a contract that bounds the time function by that constant.

```coq
  Parameter T_get : forall {A : Type}, K.t -> t A -> N.
  Parameter T_set : forall {A : Type}, K.t -> A -> t A -> N.
  Parameter c_map : N.
  Parameter T_get_le :
    forall A k (m : t A), (T_get k m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
```

- An implementation (`TrieMap`) runs `TimeFun get set`. That defines `T_get` and `T_set`, the names the signature expects. It then proves the contracts for its own `c_map`.
- A client functor (`SumValues`) runs `TimeFun` on its own functions. A call of `M.get` is charged with `M.T_get`, so the client's bound can use only the contract.
- In `SumValues`, `sum_values ks m` adds the values that `m` holds at the keys `ks`, and `key_work ks` is the total bit length of the encoded keys, each plus one.

```coq
  Theorem T_sum_values_le (ks : list M.K.t) (m : M.t nat) :
    (T_sum_values ks m <=
     (M.c_map + 2) * N.of_nat (key_work ks) + N.of_nat (sum_values ks m) + 1)%N.
```

- The bound holds for every implementation of the signature.
- The contracts are `Parameter`s of a module type, so they add no axiom: every instance proves them.
- A record of functions, which can't be stored in data (step 5), becomes a functor parameter the same way.

## 9. Loops

[`examples/Loops.v`](../examples/Loops.v) uses `Argent.Loop` for loops that don't recurse on a smaller piece of their input.

- `loop` recurses on a proof that the state decreases (an accessibility proof).
- `loop_fuel` takes a `nat` bound on the number of iterations (fuel).
- Each iteration calls a step function, which continues with a smaller state or stops with a result.

```coq
Definition count_step (n : nat) : {m : nat | m < n} + nat :=
  match n as k return {m : nat | m < k} + nat with
  | 0 => inr 0
  | S m => inl (exist _ m (PeanoNat.Nat.lt_succ_diag_r m))
  end.
```

```coq
Definition countdown (n : nat) : nat := loop lt count_step n (Acc_intro_generator 32 lt_wf n).
```

- `Acc_intro_generator 32 lt_wf` puts `2 ^ 32` constructors in front of the proof `lt_wf`, built lazily. `loop` recurses on them under `vm_compute` without reducing the proof itself. This matters when a proof doesn't compute, as in step 10.
- Extraction erases the proof. The extracted `loop` is a plain recursive function with no fuel, and `countdown` calls it.

The bound of a loop comes from a potential `Phi` on states (`T_loop_le`, or `T_loop_fuel_le` for fuel):

- Each step that continues must make `Phi` drop by more than the step costs.
- The step that stops must cost at most `Tstop`.
- Then the loop from `s` costs at most `Phi s + Tstop + 1`, for every proof and every amount of fuel.
- For the countdown, `Phi k = 2 * k` pays for each step and for its call.

```coq
Theorem T_countdown_le (n : nat) : (T_countdown n <= 2 * N.of_nat n + 3)%N.
Proof.
  rewrite T_countdown_unfold.
  (* [T_loop_le] bounds the loop by [Phi n + Tstop + 1], with [Phi k = 2 * k] and [Tstop = 1]. *)
  enough (Hloop : (T_loop lt count_step T_count_step n (Acc_intro_generator 32 lt_wf n)
                   <= 2 * N.of_nat n + 1 + 1)%N) by lia.
  apply (T_loop_le lt count_step T_count_step (fun _ => True) (fun k => 2 * N.of_nat k)%N 1%N).
  - (* A step from [S k] continues with [k]: it costs 1, and the potential drops by 2. *)
    intros [| k] s1 Hlt _ Hstep; cbn in Hstep; [discriminate |].
    injection Hstep as <-. split; [exact I |]. time_simpl. lia.
  - (* The step at 0 stops, and costs 1. *)
    intros s r _ _. time_simpl. lia.
  - (* The invariant is [True]. *)
    exact I.
Qed.
```

- `T_countdown_unfold`: `T_countdown` is one step for the call, plus the time function of `loop`.
- `time_simpl` replaces a time function whose value is a number, here `T_count_step`, by that number.
- The tactic `loop_bound` applies `T_loop_le` or `T_loop_fuel_le`. `T_count_le`, in the same file, uses it.

## 10. Well-founded recursion

[`examples/Halving.v`](../examples/Halving.v) has a binary logarithm that recurses on half of its argument. Half of a number isn't a structural subterm, so the definition uses `Fix` over `N.lt`. Each recursive call needs a proof that its argument is smaller:

```coq
Definition log2_step (x : N) (rec : forall y : N, (y < x)%N -> nat) : nat :=
  match x as x' return x = x' -> nat with
  | N0 => fun _ => 0
  | N.pos q => fun E =>
    match q with
    | xH => 0
    | _ => S (rec (N.div2 x) (div2_lt x q E))
    end
  end eq_refl.
```

```coq
Definition log2 (x : N) : nat :=
  Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => nat) log2_step x.
```

- The clause `return x = x' -> nat`, with `eq_refl` after the match, gives each branch an equation for its case, here `E : x = N.pos q`. The proof of decrease needs it. This pattern is called a convoy match.
- `TimeFun log2_step` gives `rec` a companion `T_rec`. A call `rec y h` costs `T_rec y h`; the proof `h` costs nothing.
- `Wf.T_Fix_le` in `Argent.Std` bounds the recursion with a potential, like the loop lemmas.
- Its premise: each step, plus 1 for its own call, costs at most `Phi x` (`T_F x rec T_rec + 1 <= Phi x`), assuming that each recursive call on `y` costs at most `Phi y + 1`.
- Its conclusion: `T_Fix … x <= Phi x + 1`.
- For `log2`, `Phi x = 4 * size x + 2`.

```coq
Theorem T_log2_le (x : N) : T_log2 x <= 4 * N.of_nat (N.size_nat x) + 4.
```

`Program Fixpoint` and `Function` build their recursion differently, and `TimeFun` rejects them with `E_WF`. Write such functions with `Fix`, `loop` or `loop_fuel`.

## 11. Before trusting a bound

A bound on `T_f` is a theorem about `T_f`. Four checks tie it to the program that runs:

- What is counted: calls under call-by-value evaluation of the extracted program. The real number of steps is at least `T_f` and at most a constant times `T_f + 1`, where the constant is the size of the largest function body involved. The design note argues this; it is not a theorem of the library.
- `TimeAudit f g …` on the extracted functions: it visits every constant they call, directly or not, checks each time function again against its constant's body, and fails on any computational constant with neither a time function nor a `TimePrim` cost. A time function edited by hand doesn't pass `TimeAudit` or `TimeCheck`.
- `TimePrim c := (e)` declares the cost of a constant without a body to read, such as one that extraction replaces by native code. It is the only way to write a cost by hand, so review every use.
- `Print Assumptions` on each bound. The contracts of a signature are `Parameter`s of a module type, not axioms. A `Parameter` outside a module type is an axiom, and `Print Assumptions` shows it.

`TimeFun` itself is an unverified Elpi program, and it is trusted. `TimeCheck` confirms only that a stored time function is what `TimeFun` produces.

## Next

- [`reference.md`](reference.md): the cost model in full, every command, tactic and bound, and the error codes.
- [`design.md`](design.md): how `TimeFun` translates a definition, and why the costs match the extracted program.
