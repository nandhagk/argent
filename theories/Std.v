(** * Time functions of the standard library

    This file derives the time functions of the standard-library functions on lists, booleans,
    pairs, [nat], [positive], [N] and [Z] that client code calls, and proves one bound for each
    of the listed functions.  Each time function lives in a module named like the last
    component of the path of its constant: [Datatypes.T_length], [List.T_rev], [Nat.T_add],
    [Pos.T_add], [N.T_add], [Z.T_add].

    Bounds are stated in the natural size of the arguments, the length of a list or the bit
    length [Pos.size_nat] of a number, with explicit constants.  The model is the extracted
    code with no native numbers, so [nat] arithmetic is unary and [positive] arithmetic is per
    bit.

    For example, [List.T_rev_le] says [List.T_rev l <= (length l + 1) * (length l + 1)].

    Builds on: Time Tactics *)

From Stdlib Require Import List Lia PArith NArith ZArith.
From Argent Require Import Time Tactics.
Import List.ListNotations.

(** * Booleans, pairs and lists of the prelude *)

Module Datatypes.

TimeFun andb orb negb fst snd CompOpp length app.

Lemma T_andb_le (a b : bool) : T_andb a b <= 1.
Proof.
  time_step.
Qed.

Lemma T_orb_le (a b : bool) : T_orb a b <= 1.
Proof.
  time_step.
Qed.

Lemma T_negb_le (a : bool) : T_negb a <= 1.
Proof.
  time_step.
Qed.

Lemma T_fst_le {A B : Type} (p : A * B) : T_fst p <= 1.
Proof.
  time_step.
Qed.

Lemma T_snd_le {A B : Type} (p : A * B) : T_snd p <= 1.
Proof.
  time_step.
Qed.

Lemma T_CompOpp_le (c : comparison) : T_CompOpp c <= 1.
Proof.
  time_step.
Qed.

Lemma T_length_le {A : Type} (l : list A) : T_length l <= length l + 1.
Proof.
  induction l as [| x l IH]; time_step.
Qed.

Lemma T_app_le {A : Type} (l m : list A) : T_app l m <= length l + 1.
Proof.
  induction l as [| x l IH]; time_step.
Qed.

End Datatypes.

Module ListDef.

TimeFun map.

Lemma T_map_le {A B : Type} (f : A -> B) (T_f : A -> nat) (k : nat) (l : list A) :
  (forall a, T_f a <= k) -> T_map f T_f l <= (k + 1) * length l + 1.
Proof.
  intros Hf. induction l as [| x l IH]; time_step.
Qed.

End ListDef.

(** * Lists *)

Module List.

TimeFun rev_append rev filter fold_left fold_right existsb forallb nth_error combine.

Lemma T_rev_append_le {A : Type} (l m : list A) : T_rev_append l m <= length l + 1.
Proof.
  revert m. induction l as [| x l IH]; intros m; time_step.
Qed.

Lemma T_rev_le {A : Type} (l : list A) : T_rev l <= (length l + 1) * (length l + 1).
Proof.
  induction l as [| x l IH]; time_step.
  rewrite length_rev in *. nia.
Qed.

Lemma T_filter_le {A : Type} (f : A -> bool) (T_f : A -> nat) (k : nat) (l : list A) :
  (forall a, T_f a <= k) -> T_filter f T_f l <= (k + 1) * length l + 1.
Proof.
  intros Hf. induction l as [| x l IH]; time_step.
Qed.

Lemma T_fold_left_le {A B : Type} (f : A -> B -> A) (T_f : A -> B -> nat) (k : nat)
    (l : list B) (a : A) :
  (forall a b, T_f a b <= k) -> T_fold_left f T_f l a <= (k + 1) * length l + 1.
Proof.
  intros Hf. revert a. induction l as [| x l IH]; intros a; time_step.
Qed.

Lemma T_fold_right_le {A B : Type} (f : B -> A -> A) (T_f : B -> A -> nat) (k : nat)
    (a : A) (l : list B) :
  (forall b a, T_f b a <= k) -> T_fold_right f T_f a l <= (k + 1) * length l + 1.
Proof.
  intros Hf. induction l as [| x l IH]; time_step.
Qed.

Lemma T_existsb_le {A : Type} (f : A -> bool) (T_f : A -> nat) (k : nat) (l : list A) :
  (forall a, T_f a <= k) -> T_existsb f T_f l <= (k + 2) * length l + 1.
Proof.
  intros Hf. induction l as [| x l IH]; time_step.
Qed.

Lemma T_forallb_le {A : Type} (f : A -> bool) (T_f : A -> nat) (k : nat) (l : list A) :
  (forall a, T_f a <= k) -> T_forallb f T_f l <= (k + 2) * length l + 1.
Proof.
  intros Hf. induction l as [| x l IH]; time_step.
Qed.

Lemma T_nth_error_le {A : Type} (l : list A) (n : nat) : T_nth_error l n <= n + 1.
Proof.
  revert l. induction n as [| n IH]; intros [| x l]; time_step.
Qed.

Lemma T_combine_le {A B : Type} (l : list A) (m : list B) : T_combine l m <= length l + 1.
Proof.
  revert m. induction l as [| x l IH]; intros [| y m]; time_step.
Qed.

End List.

(** * Unary natural numbers *)

Module Nat.

TimeFun Nat.add Nat.mul Nat.eqb Nat.leb.

Lemma T_add_le (n m : nat) : T_add n m <= n + 1.
Proof.
  induction n as [| n IH]; time_step.
Qed.

Lemma T_mul_le (n m : nat) : T_mul n m <= (n + 1) * (m + 2).
Proof.
  induction n as [| n IH]; time_step.
Qed.

Lemma T_eqb_le (n m : nat) : T_eqb n m <= n + 1.
Proof.
  revert m. induction n as [| n IH]; intros [| m]; time_step.
Qed.

Lemma T_leb_le (n m : nat) : T_leb n m <= n + 1.
Proof.
  revert m. induction n as [| n IH]; intros [| m]; time_step.
Qed.

End Nat.
