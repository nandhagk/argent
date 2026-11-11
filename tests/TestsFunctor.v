(** * Functor tests

    This file checks that [TimeFun] works inside functors.  A call of a parameter's operation
    [L.join] uses the parameter's time function [L.T_join], found by the sibling rule, and a
    functor instance carries the derived time functions of its body.  A bound proved inside the
    functor uses only the contracts of the signature.

    For example, after [Module I := JoinAll BoolLattice], [I.T_join_all] calls
    [BoolLattice.T_join].

    Builds on: Time Tactics Std *)

From Stdlib Require Import List Lia.
From Argent Require Import Time Tactics Std.
Import List.ListNotations.

Module Type LATTICE.
  Parameter t : Type.
  Parameter join : t -> t -> t.
  Parameter T_join : t -> t -> nat.
  Parameter c_join : nat.
  Parameter T_join_le : forall a b, T_join a b <= c_join.
End LATTICE.

Module JoinAll (L : LATTICE).

  Fixpoint join_all (acc : L.t) (l : list L.t) : L.t :=
    match l with
    | [] => acc
    | y :: r => join_all (L.join acc y) r
    end.

  TimeFun join_all.

  Definition join3 (a b c : L.t) : L.t := L.join (L.join a b) c.

  TimeFun join3.

  TimeCheck join_all join3.

  (** The bound uses only the contract [L.T_join_le], posed by [time_step] through the sibling
      rule. *)
  Lemma T_join_all_le (acc : L.t) (l : list L.t) :
    T_join_all acc l <= (L.c_join + 1) * length l + 1.
  Proof.
    revert acc. induction l as [| y r IH]; intros acc; time_step.
  Qed.

End JoinAll.

Module BoolLattice <: LATTICE.
  Definition t : Type := bool.
  Definition join (a b : t) : t := orb a b.
  TimeFun join.
  Definition c_join : nat := 2.
  Lemma T_join_le (a b : t) : T_join a b <= c_join.
  Proof.
    unfold c_join. time_step.
  Qed.
End BoolLattice.

Module I := JoinAll BoolLattice.

Example instance_cost : I.T_join_all false [true; false; true] = 1 + 3 * (2 + 1) := eq_refl.

(** A client of the instance finds [I.T_join_all] by the sibling rule. *)
Definition use_instance (l : list bool) : bool := I.join_all false l.

TimeFun use_instance.

Example use_instance_cost : T_use_instance [true] = 1 + I.T_join_all false [true] := eq_refl.
