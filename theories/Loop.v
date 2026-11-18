(** * Loops

    A loop whose state does not get structurally smaller is not a [Fixpoint] that Rocq accepts.
    This file gives two ways to write such a loop, and a lemma that bounds the time of each.
    - [loop] takes a step function that returns either a smaller state, with a proof that it is
      smaller, or a result.  It recurses on an accessibility proof, which extraction erases, so
      the extracted code is a plain recursive function without fuel.
    - [loop_fuel] runs the step function at most [fuel] times, with fuel computed from the data.
    Both bounds come from a potential [Phi]: each step must pay its own cost and the cost of its
    call from a strict decrease of [Phi].  So the bounds hold for every accessibility proof and
    every amount of fuel.

    For example, a countdown whose step goes from [n + 1] to [n] and costs 1 meets the premises
    of [T_loop_le] with the potential [fun n => 2 * n] and a last step of cost 1.  So the
    countdown from [n] costs at most [2 * n + 2].

    Builds on: Time *)

From Stdlib Require Import Lia NArith.
From Argent Require Import Time.

(** Induction on accessibility proofs, with a motive that depends on the proof.  The proof of
    [T_loop_le] uses it. *)
Scheme Acc_ind_dep := Induction for Acc Sort Prop.

(** * The accessibility loop *)

(** Run [step] from [s] until it returns a result [inr r].  A step that continues returns a
    smaller state [s1] with a proof [Hlt : lt s1 s], so the recursion follows the accessibility
    proof [H] down. *)
Fixpoint loop {S R : Type} (lt : S -> S -> Prop) (step : forall s, {s1 : S | lt s1 s} + R)
    (s : S) (H : Acc lt s) {struct H} : R :=
  match step s with
  | inl (exist _ s1 Hlt) => loop lt step s1 (Acc_inv H Hlt)
  | inr r => r
  end.

TimeFun loop.

(** When each continuing step keeps [Inv] and pays its cost and its call from a strict decrease
    of [Phi], and the last step costs at most [Tstop], the whole loop from [s] costs at most
    [Phi s + Tstop + 1]. *)
Theorem T_loop_le {S R : Type} (lt : S -> S -> Prop)
    (step : forall s, {s1 : S | lt s1 s} + R) (T_step : S -> N) (Inv : S -> Prop)
    (Phi : S -> N) (Tstop : N) :
  (forall s s1 Hlt, Inv s -> step s = inl (exist _ s1 Hlt) ->
    Inv s1 /\ (T_step s + Phi s1 < Phi s)%N) ->
  (forall s r, Inv s -> step s = inr r -> (T_step s <= Tstop)%N) ->
  forall s (H : Acc lt s), Inv s -> (T_loop lt step T_step s H <= Phi s + Tstop + 1)%N.
Proof.
  intros Hgo Hstop s H. induction H as [s Hacc IH] using Acc_ind_dep. intros Hinv.
  time_unfold @T_loop. cbn [Acc_inv]. destruct (step s) as [[s1 Hlt] | r] eqn:Hstep.
  - destruct (Hgo s s1 Hlt Hinv Hstep) as [Hinv1 Hdec].
    specialize (IH s1 Hlt Hinv1). lia.
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

(** The bound of [T_loop_le] for the fuel loop.  It holds for every amount of fuel. *)
Theorem T_loop_fuel_le {St R : Type} (step : St -> St + R) (T_step : St -> N)
    (Inv : St -> Prop) (Phi : St -> N) (Tstop : N) :
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ (T_step s + Phi s1 < Phi s)%N) ->
  (forall s r, Inv s -> step s = inr r -> (T_step s <= Tstop)%N) ->
  forall fuel s, Inv s -> (T_loop_fuel step T_step fuel s <= Phi s + Tstop + 1)%N.
Proof.
  intros Hgo Hstop fuel. induction fuel as [| fuel IH]; intros s Hinv;
    time_unfold @T_loop_fuel.
  - lia.
  - destruct (step s) as [s1 | r] eqn:Hstep.
    + destruct (Hgo s s1 Hinv Hstep) as [Hinv1 Hdec]. specialize (IH s1 Hinv1). lia.
    + specialize (Hstop s r Hinv Hstep). lia.
Qed.
