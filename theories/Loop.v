(** * Loops

    This file defines two loop combinators and bounds their derived time functions by a
    potential.  [loop] recurses structurally on an accessibility proof, so it needs no fuel and
    extracts to a plain recursive OCaml function.  [loop_fuel] takes [nat] fuel computed from
    data.  Both bounds are independent of the proof and of the fuel: every iteration pays its
    step and its own call from the decrease of the potential.

    For example, a countdown whose step maps [n + 1] to [n] and stops at 0 satisfies the
    lemmas with the potential [fun n => 2 * n] and a stop cost of 1.

    Builds on: Time *)

From Stdlib Require Import Lia.
From Argent Require Import Time.

Scheme Acc_ind_dep := Induction for Acc Sort Prop.

(** * The accessibility loop *)

(** Iterate [step] from [s] until it returns a result.  A continuing step returns a smaller
    state, so the recursion descends through the accessibility proof. *)
Fixpoint loop {S R : Type} (lt : S -> S -> Prop) (step : forall s, {s1 : S | lt s1 s} + R)
    (s : S) (H : Acc lt s) {struct H} : R :=
  match step s with
  | inl (exist _ s1 Hlt) => loop lt step s1 (Acc_inv H Hlt)
  | inr r => r
  end.

TimeFun loop.

(** Each continuing step keeps [Inv] and pays its cost and its call from a strict decrease of
    [Phi], and a stopping step costs at most [Tstop]; then the whole loop costs at most
    [Phi s + Tstop + 1]. *)
Theorem T_loop_le {S R : Type} (lt : S -> S -> Prop)
    (step : forall s, {s1 : S | lt s1 s} + R) (T_step : S -> nat) (Inv : S -> Prop)
    (Phi : S -> nat) (Tstop : nat) :
  (forall s s1 Hlt, Inv s -> step s = inl (exist _ s1 Hlt) ->
    Inv s1 /\ T_step s + Phi s1 < Phi s) ->
  (forall s r, Inv s -> step s = inr r -> T_step s <= Tstop) ->
  forall s (H : Acc lt s), Inv s -> T_loop lt step T_step s H <= Phi s + Tstop + 1.
Proof.
  intros Hgo Hstop s H. induction H as [s Hacc IH] using Acc_ind_dep. intros Hinv.
  cbn [T_loop]. destruct (step s) as [[s1 Hlt] | r] eqn:Hstep.
  - destruct (Hgo s s1 Hlt Hinv Hstep) as [Hinv1 Hdec].
    specialize (IH s1 Hlt Hinv1). cbn [Acc_inv]. lia.
  - specialize (Hstop s r Hinv Hstep). lia.
Qed.

(** * The fuel loop *)

(** Iterate [step] from [s] at most [fuel] times.  [inl s] is the state where the fuel ran
    out, and [inr r] is a result. *)
Fixpoint loop_fuel {St R : Type} (step : St -> St + R) (fuel : nat) (s : St) : St + R :=
  match fuel with
  | 0 => inl s
  | S f =>
    match step s with
    | inl s1 => loop_fuel step f s1
    | inr r => inr r
    end
  end.

TimeFun loop_fuel.

(** The bound of [T_loop_le] for the fuel loop; it holds for every amount of fuel. *)
Theorem T_loop_fuel_le {St R : Type} (step : St -> St + R) (T_step : St -> nat)
    (Inv : St -> Prop) (Phi : St -> nat) (Tstop : nat) :
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ T_step s + Phi s1 < Phi s) ->
  (forall s r, Inv s -> step s = inr r -> T_step s <= Tstop) ->
  forall fuel s, Inv s -> T_loop_fuel step T_step fuel s <= Phi s + Tstop + 1.
Proof.
  intros Hgo Hstop fuel. induction fuel as [| fuel IH]; intros s Hinv; cbn [T_loop_fuel].
  - lia.
  - destruct (step s) as [s1 | r] eqn:Hstep.
    + destruct (Hgo s s1 Hinv Hstep) as [Hinv1 Hdec]. specialize (IH s1 Hinv1). lia.
    + specialize (Hstop s r Hinv Hstep). lia.
Qed.
