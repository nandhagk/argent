(** * Program Fixpoint and Function

    This file records what [TimeFun] does with the two commands that define functions by
    well-founded recursion.  [Program Fixpoint] goes through [Fix_sub], which has no time
    function, and [TimeFun] rejects it with [E_WF] before translation.  [Function] goes through
    a termination term [half_fn_terminate] whose fixpoint over the accessibility proof builds a
    proof together with the result in nested convoy matches, which the translation does not
    support, so [TimeFun] rejects its caller with [E_WF] and the term itself with [E_TERM].
    Both messages say to write the definition with [Fix], [loop] or [loop_fuel].

    For example, [half_pf 5] is 2, and [TimeFun half_pf] fails with [E_WF].

    Builds on: Time Std *)

From Stdlib Require Import Lia Program.Wf Recdef.
From Argent Require Import Time Std.

Program Fixpoint half_pf (n : nat) {measure n} : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S m) => S (half_pf m)
  end.

Fail TimeFun half_pf.

TimeFunFails "E_WF" half_pf.

Function half_fn (n : nat) {measure (fun k => k) n} : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S m) => S (half_fn m)
  end.
Proof.
  intros. lia.
Defined.

Fail TimeFun half_fn.

TimeFunFails "E_WF" half_fn.

Fail TimeFun half_fn_terminate.

TimeFunFails "E_TERM" half_fn_terminate.
