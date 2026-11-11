(** * Tests of the bounds of Std

    This file checks that the bounds of [Argent.Std] on [N] and [Z] are found by [time_step] in
    a client.  Each client function calls standard-library functions on its own arguments, and
    its bound follows in one line from the sibling lemmas [T_g_le] of the callees.  The bounds
    that a later bound of Std already uses, such as [Pos.T_iter_le] in [Z.T_shiftl_le], are not
    repeated here.

    For example, [T_use_gcd_le] bounds a call of [Z.gcd] by a quadratic in the bit lengths of
    its arguments.

    Builds on: Time Tactics Std *)

From Stdlib Require Import Lia PArith NArith ZArith.
From Argent Require Import Time Tactics Std.

(** * N *)

Definition use_N (n m : N) : bool * N * N * nat * N :=
  (N.leb n m, N.succ n, N.pred n, N.size_nat m, N.div2 m).

TimeFun use_N.

Lemma T_use_N_le (n m : N) : T_use_N n m <= 3 * N.size_nat n + N.size_nat m + 10.
Proof.
  time_step.
Qed.

Definition use_pos_eqb (p q : positive) : bool := Pos.eqb p q.

TimeFun use_pos_eqb.

Lemma T_use_pos_eqb_le (p q : positive) : T_use_pos_eqb p q <= Pos.size_nat p + 1.
Proof.
  time_step.
Qed.

(** * Z *)

Definition use_succ_pred (x : Z) : Z * Z := (Z.succ x, Z.pred x).

TimeFun use_succ_pred.

Lemma T_use_succ_pred_le (x : Z) : T_use_succ_pred x <= 6 * Z.size_nat x + 11.
Proof.
  time_step.
Qed.

Definition use_bits (x y : Z) : Z * Z * Z := (Z.land x y, Z.lor x y, Z.lxor x y).

TimeFun use_bits.

Lemma T_use_bits_le (x y : Z) : T_use_bits x y <= 12 * (Z.size_nat x + Z.size_nat y) + 25.
Proof.
  time_step.
Qed.

Definition use_shiftr (x y : Z) : Z := Z.shiftr x y.

TimeFun use_shiftr.

Lemma T_use_shiftr_le (x y : Z) :
  T_use_shiftr x y <= (Z.size_nat x + 5) * Z.abs_nat y + 4.
Proof.
  time_step.
Qed.

Definition use_div (x y : Z) : Z * Z := (Z.div x y, Z.modulo x y).

TimeFun use_div.

Lemma T_use_div_le (x y : Z) :
  T_use_div x y <= 32 * (Z.size_nat x + 1) * (Z.size_nat x + Z.size_nat y + 2) + 3.
Proof.
  time_step.
Qed.

Definition use_gcd (x y : Z) : Z := Z.gcd x y.

TimeFun use_gcd.

Lemma T_use_gcd_le (x y : Z) :
  T_use_gcd x y <=
  (Z.size_nat x + Z.size_nat y + 2) * (2 * (Z.size_nat x + Z.size_nat y) + 3) + 3.
Proof.
  time_step.
Qed.
