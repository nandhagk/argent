(** * Functor tests

    This file checks that [TimeFun] works inside functors.  A call of a parameter's operation
    [L.join] uses the parameter's time function [L.T_join], found by the sibling rule, and a
    functor instance carries the derived time functions of its body.  A bound proved inside the
    functor uses only the contracts of the signature.  A time function found beside a callee
    with a body is derived again before it is used, also through [Include] and in an instance.

    For example, after [Module I := JoinAll BoolLattice], [I.T_join_all] calls
    [BoolLattice.T_join].

    Builds on: Time Tactics Std *)

From Stdlib Require Import List PArith NArith Lia.
From Argent Require Import Time Tactics Std.
Import List.ListNotations.

Module Type LATTICE.
  Parameter t : Type.
  Parameter join : t -> t -> t.
  Parameter T_join : t -> t -> N.
  Parameter c_join : N.
  Parameter T_join_le : forall a b, (T_join a b <= c_join)%N.
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
    (T_join_all acc l <= (L.c_join + 1) * N.of_nat (length l) + 1)%N.
  Proof.
    revert acc. induction l as [| y r IH]; intros acc; time_step.
  Qed.

End JoinAll.

Module BoolLattice <: LATTICE.
  Definition t : Type := bool.
  Definition join (a b : t) : t := orb a b.
  TimeFun join.
  Definition c_join : N := 2%N.
  Lemma T_join_le (a b : t) : (T_join a b <= c_join)%N.
  Proof.
    unfold c_join. time_step.
  Qed.
End BoolLattice.

Module I := JoinAll BoolLattice.

Example instance_cost : I.T_join_all false [true; false; true] = (1 + 3 * (2 + 1))%N := eq_refl.

(** A client of the instance finds [I.T_join_all] by the sibling rule. *)
Definition use_instance (l : list bool) : bool := I.join_all false l.

TimeFun use_instance.

Example use_instance_cost : T_use_instance [true] = (1 + I.T_join_all false [true])%N := eq_refl.

(** * Checked sibling time functions

    [TimeFun] derives again the time function that it finds beside a callee by the sibling rule
    when that time function has a body.  A parameter of a signature, such as [K.T_encode], has
    none and is used as it is.  The definitions below come into a timed functor by [Include]
    from a functor that holds only code, and the instance [FP] is used from outside. *)

Module Type KEY_OPS.
  Parameter t : Type.
  Parameter encode : t -> positive.
End KEY_OPS.

Module Type KEY_T.
  Include KEY_OPS.
  Parameter T_encode : t -> N.
End KEY_T.

Module FooCode (K : KEY_OPS).
  Definition twice (k : K.t) : positive := Pos.add (K.encode k) (K.encode k).
End FooCode.

Module Foo (K : KEY_OPS).
  Include FooCode K.
End Foo.

Module FooT (K : KEY_T).
  Include Foo K.

  TimeFun twice.

  Definition quad (k : K.t) : positive := Pos.add (twice k) (twice k).

  TimeFun quad.

  (** A hand-written time function in a functor body is caught. *)
  Definition cheat (k : K.t) : positive := twice k.

  Definition T_cheat (k : K.t) : N := 0%N.

  Definition use_cheat (k : K.t) : positive := cheat k.

  Fail TimeFun use_cheat.

  TimeFunFails "E_CHECK" use_cheat.
End FooT.

Module PosKey <: KEY_T.
  Definition t : Type := positive.
  Definition encode (p : t) : positive := p.
  TimeFun encode.
End PosKey.

Module FP := FooT PosKey.

Definition use_quad (p : positive) : positive := FP.quad p.

TimeFun use_quad.

Example use_quad_cost : T_use_quad 1%positive = (1 + FP.T_quad 1%positive)%N := eq_refl.

TimeCheck use_quad.

TimeAudit use_quad.

(** The hand-written time function is caught in the instance as well. *)
Definition use_instance_cheat (p : positive) : positive := FP.cheat p.

TimeFunFails "E_CHECK" use_instance_cheat.

(** * Contracts with abstract constants

    A contract multiplies an abstract constant of the signature by a size.  [time_step]
    distributes the products, adds the monotone consequences [c * a <= c * b] of the hypotheses
    [a <= b], replaces the remaining products by variables and calls [lia]. *)

Module Type TWO_COSTS.
  Parameter f : nat -> nat.
  Parameter g : nat -> nat.
  Parameter T_f : nat -> N.
  Parameter T_g : nat -> N.
  Parameter c1 : N.
  Parameter c2 : N.
  Parameter T_f_le : forall n, (T_f n <= c1 * (N.of_nat n + 1))%N.
  Parameter T_g_le : forall n, (T_g n <= c2 * (N.of_nat n + 1))%N.
End TWO_COSTS.

Module UseTwo (M : TWO_COSTS).
  Definition both (n m : nat) : nat * nat := (M.f n, M.g m).

  TimeFun both.

  Lemma T_both_le (n m : nat) :
    (T_both n m <= M.c1 * (N.of_nat n + 1) + M.c2 * (N.of_nat m + 1) + 1)%N.
  Proof.
    time_step.
  Qed.

  Definition twice_f (n m : nat) : nat * nat := (M.f n, M.f m).

  TimeFun twice_f.

  (** The bound needs [M.c1 * N.of_nat n <= M.c1 * N.of_nat m] from [n <= m] on [nat]. *)
  Lemma T_twice_f_le (n m : nat) :
    n <= m -> (T_twice_f n m <= 2 * M.c1 * (N.of_nat m + 1) + 1)%N.
  Proof.
    intros Hnm. time_step.
  Qed.

  (** A bound that does not hold leaves the goal as [time_step] found it, with its products. *)
  Lemma T_twice_f_wrong (n : nat) : (T_twice_f n n <= M.c1 * N.of_nat n)%N.
  Proof.
    time_step.
    lazymatch goal with
    | |- context [(M.c1 * _)%N] => idtac
    end.
    assert_fails (clear time_prod).
  Abort.
End UseTwo.

(** [time_lin] alone closes a goal that needs the monotone consequence [c * a <= c * b] of
    [a <= b] for the folded constant [c], and fails on products that it cannot relate. *)
Definition c : N := 3%N.

Example time_lin_mono (a b t : N) : (a <= b -> t <= c * (a + 1) -> t <= c * (b + 1))%N.
Proof.
  intros Hab Ht. time_lin.
Qed.

Example time_lin_fails (a b : N) : (c * a <= c * b)%N.
Proof.
  Fail time_lin.
Abort.
