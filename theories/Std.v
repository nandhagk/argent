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

(** * Binary positive numbers *)

Module Pos.

TimeFun Pos.succ Pos.add Pos.pred_double Pos.pred_N Pos.eqb Pos.compare_cont Pos.compare
  Pos.leb Pos.ltb Pos.size_nat Pos.mul Pos.double_mask Pos.succ_double_mask
  Pos.double_pred_mask Pos.sub_mask Pos.sub Pos.Ndouble Pos.Nsucc_double Pos.land Pos.lor
  Pos.lxor Pos.ldiff Pos.iter Pos.div2 Pos.div2_up Pos.pred Pos.gcdn Pos.gcd Pos.shiftl.

Lemma T_succ_le (p : positive) : T_succ p <= Pos.size_nat p.
Proof.
  induction p as [p IH | p IH |]; time_step.
Qed.

(** [Pos.add] and [Pos.add_carry] are one mutual block, so their bounds are proved together. *)
Lemma T_add_carry_both (p q : positive) :
  T_add p q <= Pos.size_nat p + Pos.size_nat q /\
  T_add_carry p q <= Pos.size_nat p + Pos.size_nat q.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |];
    time_unfold T_add; time_unfold T_add_carry; cbn [Pos.size_nat]; try specialize (IH q);
    try pose proof (T_succ_le p); try pose proof (T_succ_le q); lia.
Qed.

Lemma T_add_le (p q : positive) : T_add p q <= Pos.size_nat p + Pos.size_nat q.
Proof.
  exact (proj1 (T_add_carry_both p q)).
Qed.

Lemma T_add_carry_le (p q : positive) : T_add_carry p q <= Pos.size_nat p + Pos.size_nat q.
Proof.
  exact (proj2 (T_add_carry_both p q)).
Qed.

Lemma T_pred_double_le (p : positive) : T_pred_double p <= Pos.size_nat p.
Proof.
  induction p as [p IH | p IH |]; time_step.
Qed.

Lemma T_eqb_le (p q : positive) : T_eqb p q <= Pos.size_nat p.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; time_step.
Qed.

Lemma T_compare_cont_le (r : comparison) (p q : positive) :
  T_compare_cont r p q <= Pos.size_nat p.
Proof.
  revert q r. induction p as [p IH | p IH |]; intros [q | q |] r; time_step.
Qed.

Lemma T_compare_le (p q : positive) : T_compare p q <= Pos.size_nat p + 1.
Proof.
  time_step.
Qed.

Lemma T_size_nat_le (p : positive) : T_size_nat p <= Pos.size_nat p.
Proof.
  induction p as [p IH | p IH |]; time_step.
Qed.

(** [Pos.size_nat p] is the bit length of [p]: [p] is below [2 ^ Pos.size_nat p], and it is the
    least such exponent. *)
Lemma size_nat_upper (p : positive) : Pos.to_nat p < 2 ^ Pos.size_nat p.
Proof.
  induction p as [p IH | p IH |]; cbn [Pos.size_nat Nat.pow];
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
Qed.

Lemma size_nat_least (p : positive) (k : nat) : Pos.to_nat p < 2 ^ k -> Pos.size_nat p <= k.
Proof.
  revert k. induction p as [p IH | p IH |]; intros [| k] Hlt; cbn [Pos.size_nat Nat.pow] in *;
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1 in Hlt;
    try pose proof (Pos2Nat.is_pos p); try lia.
  - specialize (IH k). lia.
  - specialize (IH k). lia.
Qed.

Lemma size_nat_mul (p q : positive) :
  Pos.size_nat (p * q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  apply size_nat_least. rewrite Pos2Nat.inj_mul, Nat.pow_add_r.
  pose proof (size_nat_upper p). pose proof (size_nat_upper q). nia.
Qed.

Lemma T_mul_le (p q : positive) :
  T_mul p q <= Pos.size_nat p * (Pos.size_nat p + 2 * Pos.size_nat q + 2).
Proof.
  induction p as [p IH | p IH |]; time_unfold T_mul; cbn [Pos.size_nat].
  - pose proof (T_add_le q (p * q)~0). pose proof (size_nat_mul p q).
    cbn [Pos.size_nat] in *. nia.
  - nia.
  - lia.
Qed.

End Pos.

(** * Binary natural numbers *)

Module N.

TimeFun N.succ_pos N.double N.succ_double N.add N.sub N.eqb N.compare N.leb N.ltb N.succ N.pred
  N.pos_div_eucl N.land N.lor N.lxor N.ldiff N.div2 N.shiftl N.shiftr N.ones N.lnot.

Lemma T_add_le (n m : N) : T_add n m <= N.size_nat n + N.size_nat m + 1.
Proof.
  destruct n, m; time_step.
Qed.

Lemma T_eqb_le (n m : N) : T_eqb n m <= N.size_nat n + 1.
Proof.
  destruct n, m; time_step.
Qed.

Lemma T_compare_le (n m : N) : T_compare n m <= N.size_nat n + 2.
Proof.
  destruct n, m; time_step.
Qed.

End N.

(** * Binary integers *)

Module Z.

TimeFun Z.double Z.succ_double Z.pred_double Z.pos_sub Z.add Z.opp Z.sub Z.compare Z.eqb
  Z.leb Z.ltb Z.min Z.max Z.mul Z.abs Z.of_N Z.pos_div_eucl Z.div_eucl Z.div Z.modulo Z.gcd
  Z.land Z.lor Z.lxor Z.div2 Z.shiftl Z.shiftr.

(** The bit length of the absolute value of an integer. *)
Definition size_nat (z : Z) : nat :=
  match z with
  | Z0 => 0
  | Zpos p => Pos.size_nat p
  | Zneg p => Pos.size_nat p
  end.

Lemma T_double_le (z : Z) : T_double z <= 1.
Proof.
  time_step.
Qed.

Lemma T_succ_double_le (z : Z) : T_succ_double z <= size_nat z + 1.
Proof.
  destruct z; time_step.
Qed.

Lemma T_pred_double_le (z : Z) : T_pred_double z <= size_nat z + 1.
Proof.
  destruct z; time_step.
Qed.

(** The number of trailing zero bits of [p]. *)
Fixpoint trailing_zeros (p : positive) : nat :=
  match p with
  | xO p => S (trailing_zeros p)
  | _ => 0
  end.

(** The trailing zero bits of the absolute value of an integer. *)
Definition trailing_zeros_z (z : Z) : nat :=
  match z with
  | Z0 => 0
  | Zpos p => trailing_zeros p
  | Zneg p => trailing_zeros p
  end.

Lemma trailing_zeros_lt (p : positive) : trailing_zeros p < Pos.size_nat p.
Proof.
  induction p as [p IH | p IH |]; cbn [trailing_zeros Pos.size_nat]; lia.
Qed.

Lemma trailing_zeros_pred_double (p : positive) : trailing_zeros (Pos.pred_double p) = 0.
Proof.
  destruct p; reflexivity.
Qed.

Lemma T_pred_double_zeros (p : positive) : Pos.T_pred_double p <= trailing_zeros p + 1.
Proof.
  induction p as [p IH | p IH |]; time_step.
Qed.

(** [Z.pos_sub] is linear only in the amortised sense: at a level whose result is about to be
    decremented, [Pos.pred_double] walks the trailing zeros of the result so far.  Those zeros
    are paid by the potential [trailing_zeros_z], which grows by at most one per level. *)
Lemma T_pos_sub_zeros (p q : positive) :
  T_pos_sub p q + trailing_zeros_z (Z.pos_sub p q) <= 3 * (Pos.size_nat p + Pos.size_nat q).
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |];
    time_unfold T_pos_sub; cbn [Z.pos_sub Pos.size_nat];
    try (generalize (IH q); destruct (Z.pos_sub p q) as [| r | r]; intros Hq);
    unfold T_double, T_succ_double, T_pred_double in *;
    cbn [Z.double Z.succ_double Z.pred_double trailing_zeros_z trailing_zeros] in *;
    rewrite ?trailing_zeros_pred_double;
    try pose proof (T_pred_double_zeros r); try pose proof (T_pred_double_zeros p);
    try pose proof (T_pred_double_zeros q);
    try pose proof (trailing_zeros_lt p); try pose proof (trailing_zeros_lt q); lia.
Qed.

Lemma T_pos_sub_le (p q : positive) :
  T_pos_sub p q <= 3 * (Pos.size_nat p + Pos.size_nat q).
Proof.
  pose proof (T_pos_sub_zeros p q). lia.
Qed.

Lemma T_add_le (x y : Z) : T_add x y <= 3 * (size_nat x + size_nat y) + 1.
Proof.
  destruct x, y; time_step.
Qed.

Lemma T_opp_le (x : Z) : T_opp x <= 1.
Proof.
  time_step.
Qed.

Lemma T_sub_le (x y : Z) : T_sub x y <= 3 * (size_nat x + size_nat y) + 3.
Proof.
  destruct x, y; time_step.
Qed.

Lemma T_compare_le (x y : Z) : T_compare x y <= size_nat x + 3.
Proof.
  destruct x, y; time_step.
Qed.

Lemma T_eqb_le (x y : Z) : T_eqb x y <= size_nat x + 1.
Proof.
  destruct x, y; time_step.
Qed.

Lemma T_leb_le (x y : Z) : T_leb x y <= size_nat x + 4.
Proof.
  time_step.
Qed.

Lemma T_ltb_le (x y : Z) : T_ltb x y <= size_nat x + 4.
Proof.
  time_step.
Qed.

Lemma T_min_le (x y : Z) : T_min x y <= size_nat x + 4.
Proof.
  time_step.
Qed.

Lemma T_max_le (x y : Z) : T_max x y <= size_nat x + 4.
Proof.
  time_step.
Qed.

Lemma T_mul_le (x y : Z) : T_mul x y <= (size_nat x + 1) * (size_nat x + 2 * size_nat y + 2).
Proof.
  destruct x, y; time_step.
Qed.

End Z.
