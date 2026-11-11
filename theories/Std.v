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


Lemma size_nat_pos (p : positive) : 1 <= Pos.size_nat p.
Proof.
  destruct p; cbn [Pos.size_nat]; lia.
Qed.

Lemma T_pred_N_le (p : positive) : T_pred_N p <= Pos.size_nat p + 1.
Proof.
  destruct p; time_step.
Qed.

Lemma T_div2_le (p : positive) : T_div2 p <= 1.
Proof.
  time_step.
Qed.

Lemma T_div2_up_le (p : positive) : T_div2_up p <= Pos.size_nat p + 1.
Proof.
  destruct p; time_step.
Qed.

(** * Bitwise operations *)

Lemma T_land_le (p q : positive) : T_land p q <= 2 * Pos.size_nat p.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; time_step.
Qed.

Lemma T_lor_le (p q : positive) : T_lor p q <= Pos.size_nat p.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; time_step.
Qed.

Lemma T_lxor_le (p q : positive) : T_lxor p q <= 2 * Pos.size_nat p.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; time_step.
Qed.

Lemma T_ldiff_le (p q : positive) : T_ldiff p q <= 2 * Pos.size_nat p.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; time_step.
Qed.

(** * Subtraction *)

Lemma T_double_mask_le (m : Pos.mask) : T_double_mask m <= 1.
Proof.
  destruct m; time_step.
Qed.

Lemma T_succ_double_mask_le (m : Pos.mask) : T_succ_double_mask m <= 1.
Proof.
  destruct m; time_step.
Qed.

Lemma T_double_pred_mask_le (p : positive) : T_double_pred_mask p <= Pos.size_nat p + 1.
Proof.
  destruct p; time_step.
Qed.

(** [Pos.sub_mask] and [Pos.sub_mask_carry] are one mutual block, so their bounds are proved
    together. *)
Lemma T_sub_mask_both (p q : positive) :
  T_sub_mask p q <= Pos.size_nat p + Pos.size_nat q /\
  T_sub_mask_carry p q <= Pos.size_nat p + Pos.size_nat q.
Proof.
  revert p. induction q as [q IH | q IH |]; intros [p | p |];
    time_unfold T_sub_mask; time_unfold T_sub_mask_carry; cbn [Pos.size_nat];
    try specialize (IH p);
    try pose proof (T_double_mask_le (Pos.sub_mask p q));
    try pose proof (T_succ_double_mask_le (Pos.sub_mask p q));
    try pose proof (T_double_mask_le (Pos.sub_mask_carry p q));
    try pose proof (T_succ_double_mask_le (Pos.sub_mask_carry p q));
    try pose proof (T_pred_double_le p); try pose proof (T_double_pred_mask_le p); lia.
Qed.

Lemma T_sub_le (p q : positive) : T_sub p q <= Pos.size_nat p + Pos.size_nat q + 1.
Proof.
  pose proof (proj1 (T_sub_mask_both p q)). time_step.
Qed.

Lemma size_nat_sub (p q : positive) : Pos.size_nat (p - q) <= Pos.size_nat p.
Proof.
  destruct (Pos.lt_total q p) as [Hlt | [Heq | Hgt]].
  - apply Pos.size_nat_monotone, Pos.sub_decr, Hlt.
  - subst. rewrite Pos.sub_diag. apply size_nat_pos.
  - rewrite Pos.sub_le by (apply Pos.lt_le_incl, Hgt). apply size_nat_pos.
Qed.

(** * Iteration and the greatest common divisor *)

Lemma T_iter_lt {A : Type} (f : A -> A) (T_f : A -> nat) (Inv : A -> Prop) (k : nat)
    (x : A) (n : positive) :
  (forall y, Inv y -> Inv (f y)) -> (forall y, Inv y -> T_f y <= k) -> Inv x ->
  T_iter f T_f x n < (k + 2) * Pos.to_nat n.
Proof.
  intros Hinv Hf. revert x. induction n as [n IH | n IH |]; intros x Hx;
    time_unfold @T_iter; rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1.
  - pose proof (Pos.iter_invariant n A f Inv Hinv x Hx) as Hx1.
    pose proof (Pos.iter_invariant n A f Inv Hinv _ Hx1) as Hx2.
    pose proof (IH x Hx). pose proof (IH _ Hx1). pose proof (Hf _ Hx2). nia.
  - pose proof (Pos.iter_invariant n A f Inv Hinv x Hx) as Hx1.
    pose proof (IH x Hx). pose proof (IH _ Hx1). nia.
  - pose proof (Hf x Hx). lia.
Qed.

(** [Pos.iter f x n] calls [f] [n] times, so its time is linear in the value of [n] when [f]
    keeps the invariant [Inv] and takes at most [k] steps on every state that satisfies it. *)
Lemma T_iter_le {A : Type} (f : A -> A) (T_f : A -> nat) (Inv : A -> Prop) (k : nat)
    (x : A) (n : positive) :
  (forall y, Inv y -> Inv (f y)) -> (forall y, Inv y -> T_f y <= k) -> Inv x ->
  T_iter f T_f x n <= (k + 2) * Pos.to_nat n.
Proof.
  intros Hinv Hf Hx. pose proof (T_iter_lt f T_f Inv k x n Hinv Hf Hx). lia.
Qed.

(** Each step of [Pos.gcdn] compares and subtracts its arguments, whose total bit length [s]
    never grows, so [n] steps take [O(n * s)] time. *)
Lemma T_gcdn_le (n : nat) (a b : positive) (s : nat) :
  Pos.size_nat a + Pos.size_nat b <= s -> T_gcdn n a b <= (n + 1) * (2 * s + 3).
Proof.
  revert a b. induction n as [| n IH]; intros a b Hs; time_unfold T_gcdn; [lia |].
  rewrite Nat.add_succ_l, Nat.mul_succ_l.
  destruct a as [a | a |], b as [b | b |]; cbn [Pos.size_nat] in Hs;
    try (pose proof (T_compare_le a b); pose proof (T_sub_le a b); pose proof (T_sub_le b a);
         pose proof (size_nat_sub a b); pose proof (size_nat_sub b a);
         destruct (a ?= b)%positive);
    repeat match goal with
           | |- context [T_gcdn n ?x ?y] =>
             let Hrec := fresh "Hrec" in
             let t := fresh "t" in
             assert (Hrec : T_gcdn n x y <= (n + 1) * (2 * s + 3))
               by (apply IH; cbn [Pos.size_nat]; lia);
             set (t := T_gcdn n x y) in *; clearbody t
           end; lia.
Qed.

(** [Pos.gcd] runs [Pos.gcdn] for the total bit length of its arguments, so it is quadratic. *)
Lemma T_gcd_le (a b : positive) :
  T_gcd a b <=
  (Pos.size_nat a + Pos.size_nat b + 2) * (2 * (Pos.size_nat a + Pos.size_nat b) + 3).
Proof.
  pose proof (T_gcdn_le (Pos.size_nat a + Pos.size_nat b) a b _ (le_n _)).
  pose proof (T_size_nat_le a). pose proof (T_size_nat_le b).
  pose proof (Nat.T_add_le (Pos.size_nat a) (Pos.size_nat b)).
  time_unfold T_gcd. nia.
Qed.

End Pos.

(** * Binary natural numbers *)

Module N.

TimeFun N.succ_pos N.double N.succ_double N.add N.sub N.eqb N.compare N.leb N.ltb N.succ N.pred
  N.pos_div_eucl N.land N.lor N.lxor N.ldiff N.div2 N.shiftl N.shiftr N.ones N.lnot N.size_nat.

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


Lemma T_size_nat_le (n : N) : T_size_nat n <= N.size_nat n + 1.
Proof.
  destruct n; time_step.
Qed.

Lemma T_succ_pos_le (n : N) : T_succ_pos n <= N.size_nat n + 1.
Proof.
  destruct n; time_step.
Qed.

Lemma T_succ_le (n : N) : T_succ n <= N.size_nat n + 1.
Proof.
  destruct n; time_step.
Qed.

Lemma T_pred_le (n : N) : T_pred n <= N.size_nat n + 2.
Proof.
  destruct n; time_step.
Qed.

Lemma T_leb_le (n m : N) : T_leb n m <= N.size_nat n + 3.
Proof.
  time_step.
Qed.

Lemma T_div2_le (n : N) : T_div2 n <= 1.
Proof.
  destruct n as [| [p | p |]]; time_step.
Qed.

Lemma T_land_le (n m : N) : T_land n m <= 2 * N.size_nat n + 1.
Proof.
  destruct n, m; time_step.
Qed.

Lemma T_lor_le (n m : N) : T_lor n m <= N.size_nat n + 1.
Proof.
  destruct n, m; time_step.
Qed.

Lemma T_lxor_le (n m : N) : T_lxor n m <= 2 * N.size_nat n + 1.
Proof.
  destruct n, m; time_step.
Qed.

Lemma T_ldiff_le (n m : N) : T_ldiff n m <= 2 * N.size_nat n + 1.
Proof.
  destruct n, m; time_step.
Qed.

(** * Bit lengths of results *)

(** Simplify the bit lengths of doubled numbers in the goal and the hypotheses. *)
Local Ltac size_simpl :=
  cbn [Pos.land Pos.lor Pos.lxor Pos.ldiff Pos.pred_N Pos.Ndouble Pos.Nsucc_double
    N.size_nat Pos.size_nat] in *.

Lemma size_nat_pred_double (p : positive) :
  Pos.size_nat (Pos.pred_double p) <= Pos.size_nat p + 1.
Proof.
  induction p as [p IH | p IH |]; cbn [Pos.pred_double Pos.size_nat]; lia.
Qed.

Lemma size_nat_pred_N (p : positive) : N.size_nat (Pos.pred_N p) <= Pos.size_nat p.
Proof.
  destruct p as [p | p |]; size_simpl; try pose proof (size_nat_pred_double p); lia.
Qed.

Lemma size_nat_land (p q : positive) : N.size_nat (Pos.land p q) <= Pos.size_nat p.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; size_simpl;
    try (specialize (IH q); destruct (Pos.land p q)); size_simpl; lia.
Qed.

Lemma size_nat_lor (p q : positive) :
  Pos.size_nat (Pos.lor p q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; size_simpl;
    try specialize (IH q); lia.
Qed.

Lemma size_nat_lxor (p q : positive) :
  N.size_nat (Pos.lxor p q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; size_simpl;
    try (specialize (IH q); destruct (Pos.lxor p q)); size_simpl; lia.
Qed.

Lemma size_nat_ldiff (p q : positive) : N.size_nat (Pos.ldiff p q) <= Pos.size_nat p.
Proof.
  revert q. induction p as [p IH | p IH |]; intros [q | q |]; size_simpl;
    try (specialize (IH q); destruct (Pos.ldiff p q)); size_simpl; lia.
Qed.

Lemma size_nat_N_land (n m : N) : N.size_nat (N.land n m) <= N.size_nat n.
Proof.
  destruct n as [| p], m as [| q]; cbn [N.land N.size_nat]; try lia. apply size_nat_land.
Qed.

Lemma size_nat_N_lor (n m : N) : N.size_nat (N.lor n m) <= N.size_nat n + N.size_nat m.
Proof.
  destruct n as [| p], m as [| q]; cbn [N.lor N.size_nat]; try lia. apply size_nat_lor.
Qed.

Lemma size_nat_N_lxor (n m : N) : N.size_nat (N.lxor n m) <= N.size_nat n + N.size_nat m.
Proof.
  destruct n as [| p], m as [| q]; cbn [N.lxor N.size_nat]; try lia. apply size_nat_lxor.
Qed.

Lemma size_nat_N_ldiff (n m : N) : N.size_nat (N.ldiff n m) <= N.size_nat n.
Proof.
  destruct n as [| p], m as [| q]; cbn [N.ldiff N.size_nat]; try lia. apply size_nat_ldiff.
Qed.

End N.

(** * Binary integers *)

Module Z.

TimeFun Z.double Z.succ_double Z.pred_double Z.pos_sub Z.add Z.opp Z.sub Z.compare Z.eqb
  Z.leb Z.ltb Z.min Z.max Z.mul Z.abs Z.of_N Z.pos_div_eucl Z.div_eucl Z.div Z.modulo Z.gcd
  Z.land Z.lor Z.lxor Z.div2 Z.shiftl Z.shiftr Z.succ Z.pred.

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


(** * Absolute value, successor, predecessor and halving *)

Lemma T_abs_le (x : Z) : T_abs x <= 1.
Proof.
  destruct x; time_step.
Qed.

Lemma T_of_N_le (n : N) : T_of_N n <= 1.
Proof.
  destruct n; time_step.
Qed.

Lemma T_succ_le (x : Z) : T_succ x <= 3 * size_nat x + 5.
Proof.
  time_step.
Qed.

Lemma T_pred_le (x : Z) : T_pred x <= 3 * size_nat x + 5.
Proof.
  time_step.
Qed.

Lemma T_div2_le (x : Z) : T_div2 x <= size_nat x + 2.
Proof.
  destruct x as [| [p | p |] | p]; time_step.
Qed.

(** * Bitwise operations *)

Lemma T_land_le (x y : Z) : T_land x y <= 4 * (size_nat x + size_nat y) + 8.
Proof.
  destruct x as [| a | a], y as [| b | b]; time_unfold T_land; time_pose;
    try pose proof (N.size_nat_pred_N a); try pose proof (N.size_nat_pred_N b);
    try pose proof (N.size_nat_N_lor (Pos.pred_N a) (Pos.pred_N b));
    cbn [size_nat N.size_nat] in *; lia.
Qed.

Lemma T_lor_le (x y : Z) : T_lor x y <= 4 * (size_nat x + size_nat y) + 8.
Proof.
  destruct x as [| a | a], y as [| b | b]; time_unfold T_lor; time_pose;
    try pose proof (N.size_nat_pred_N a); try pose proof (N.size_nat_pred_N b);
    try pose proof (N.size_nat_N_ldiff (Pos.pred_N a) (N.pos b));
    try pose proof (N.size_nat_N_ldiff (Pos.pred_N b) (N.pos a));
    try pose proof (N.size_nat_N_land (Pos.pred_N a) (Pos.pred_N b));
    cbn [size_nat N.size_nat] in *; lia.
Qed.

Lemma T_lxor_le (x y : Z) : T_lxor x y <= 4 * (size_nat x + size_nat y) + 8.
Proof.
  destruct x as [| a | a], y as [| b | b]; time_unfold T_lxor; time_pose;
    try pose proof (N.size_nat_pred_N a); try pose proof (N.size_nat_pred_N b);
    try pose proof (N.size_nat_N_lxor (N.pos a) (Pos.pred_N b));
    try pose proof (N.size_nat_N_lxor (Pos.pred_N a) (N.pos b));
    cbn [size_nat N.size_nat] in *; lia.
Qed.


(** * Shifts *)

Lemma T_mul_two_le (x : Z) : T_mul 2 x <= 3.
Proof.
  destruct x; time_unfold T_mul; cbn; [lia | |];
    time_unfold Pos.T_mul; time_unfold Pos.T_mul; cbn; lia.
Qed.

Lemma size_nat_succ (p : positive) : Pos.size_nat (Pos.succ p) <= Pos.size_nat p + 1.
Proof.
  induction p as [p IH | p IH |]; cbn [Pos.succ Pos.size_nat]; lia.
Qed.

Lemma size_nat_div2 (x : Z) : size_nat (Z.div2 x) <= size_nat x.
Proof.
  destruct x as [| [p | p |] | [p | p |]]; cbn [Z.div2 Pos.div2 Pos.div2_up size_nat Pos.size_nat];
    try pose proof (size_nat_succ p); lia.
Qed.

(** [Z.shiftl a n] calls [Z.mul 2] or [Z.div2] [|n|] times.  A halving of a negative number
    may carry through its bits, so a right shift of a negative [a] is bounded by the product of
    the bit length of [a] and the shift amount. *)
Lemma T_shiftl_le (a n : Z) : T_shiftl a n <= (size_nat a + 5) * Z.abs_nat n + 1.
Proof.
  time_unfold T_shiftl. destruct n as [| p | p]; cbn [Z.abs_nat]; [lia | |].
  - pose proof (Pos.T_iter_le (Z.mul 2) (fun x => T_mul 2 x) (fun _ => True) 3 a p
      (fun _ _ => I) (fun x _ => T_mul_two_le x) I). nia.
  - pose proof (Pos.T_iter_le Z.div2 (fun x => T_div2 x) (fun x => size_nat x <= size_nat a)
      (size_nat a + 2) a p) as Hiter.
    assert (Hk : forall x, size_nat x <= size_nat a -> size_nat (Z.div2 x) <= size_nat a)
      by (intros x Hx; pose proof (size_nat_div2 x); lia).
    assert (Hf : forall x, size_nat x <= size_nat a -> T_div2 x <= size_nat a + 2)
      by (intros x Hx; pose proof (T_div2_le x); lia).
    specialize (Hiter Hk Hf (le_n _)). nia.
Qed.

Lemma T_shiftr_le (a n : Z) : T_shiftr a n <= (size_nat a + 5) * Z.abs_nat n + 3.
Proof.
  time_unfold T_shiftr. pose proof (T_opp_le n). pose proof (T_shiftl_le a (- n)).
  destruct n; cbn [Z.opp Z.abs_nat] in *; lia.
Qed.


(** * Division *)

Lemma size_nat_mono (x y : Z) : (0 <= x <= y)%Z -> size_nat x <= size_nat y.
Proof.
  intros [Hx Hxy]. destruct x as [| p | p], y as [| q | q]; cbn [size_nat]; try lia.
  destruct (proj1 (Pos.le_lteq p q) Hxy) as [Hlt | Heq].
  - apply Pos.size_nat_monotone, Hlt.
  - subst. lia.
Qed.

Lemma size_nat_double (x : Z) : (0 <= x)%Z -> size_nat (2 * x) <= size_nat x + 1.
Proof.
  intros Hx. destruct x; cbn [Z.mul Pos.mul size_nat Pos.size_nat]; lia.
Qed.

Lemma size_nat_succ_double (x : Z) : (0 <= x)%Z -> size_nat (2 * x + 1) <= size_nat x + 1.
Proof.
  intros Hx. destruct x; cbn [Z.mul Z.add Pos.mul Pos.add size_nat Pos.size_nat]; lia.
Qed.

(** The quotient and the remainder of [Z.pos_div_eucl a b] are no longer than [a] and [b]. *)
Lemma pos_div_eucl_sizes (a : positive) (b : Z) :
  (0 < b)%Z ->
  (0 <= fst (Z.pos_div_eucl a b))%Z /\ (0 <= snd (Z.pos_div_eucl a b))%Z /\
  size_nat (fst (Z.pos_div_eucl a b)) <= Pos.size_nat a /\
  size_nat (snd (Z.pos_div_eucl a b)) <= size_nat b.
Proof.
  intros Hb. pose proof (Z.pos_div_eucl_bound a b Hb) as Hr.
  pose proof (Z.pos_div_eucl_eq a b Hb) as Heq.
  destruct (Z.pos_div_eucl a b) as [q r]. cbn [fst snd] in *.
  assert (Hq : (0 <= q <= Z.pos a)%Z) by nia.
  split; [lia | split; [lia | split]].
  - apply (size_nat_mono q (Z.pos a)), Hq.
  - apply size_nat_mono. lia.
Qed.

(** Each bit of [a] costs a doubling, a comparison and a subtraction, which are linear in the
    bit lengths of the partial quotient and remainder. *)
Lemma T_pos_div_eucl_le (a : positive) (b : Z) :
  (0 < b)%Z ->
  T_pos_div_eucl a b <= 16 * Pos.size_nat a * (Pos.size_nat a + size_nat b + 1).
Proof.
  intros Hb. induction a as [a IH | a IH |]; time_unfold T_pos_div_eucl;
    cbn [Pos.size_nat].
  - destruct (pos_div_eucl_sizes a b Hb) as (Hq0 & Hr0 & Hq & Hr).
    destruct (Z.pos_div_eucl a b) as [q r]. cbn [fst snd] in *.
    pose proof (T_mul_two_le r). pose proof (T_mul_two_le q).
    pose proof (T_add_le (2 * r) 1). pose proof (T_add_le (2 * q) 1).
    pose proof (T_ltb_le (2 * r + 1) b). pose proof (T_sub_le (2 * r + 1) b).
    pose proof (size_nat_double r Hr0). pose proof (size_nat_double q Hq0).
    pose proof (size_nat_succ_double r Hr0). cbn [size_nat Pos.size_nat] in *.
    destruct (2 * r + 1 <? b)%Z; lia.
  - destruct (pos_div_eucl_sizes a b Hb) as (Hq0 & Hr0 & Hq & Hr).
    destruct (Z.pos_div_eucl a b) as [q r]. cbn [fst snd] in *.
    pose proof (T_mul_two_le r). pose proof (T_mul_two_le q).
    pose proof (T_add_le (2 * q) 1).
    pose proof (T_ltb_le (2 * r) b). pose proof (T_sub_le (2 * r) b).
    pose proof (size_nat_double r Hr0). pose proof (size_nat_double q Hq0).
    cbn [size_nat Pos.size_nat] in *.
    destruct (2 * r <? b)%Z; lia.
  - pose proof (T_leb_le 2 b). cbn [size_nat Pos.size_nat] in *. lia.
Qed.


(** [Z.div_eucl] divides the absolute values and corrects the signs, which is linear. *)
Lemma T_div_eucl_le (a b : Z) :
  T_div_eucl a b <= 16 * (size_nat a + 1) * (size_nat a + size_nat b + 2).
Proof.
  destruct a as [| a | a], b as [| b | b]; time_unfold T_div_eucl; cbn [size_nat];
    try lia;
    pose proof (T_pos_div_eucl_le a _ (eq_refl : (0 < Z.pos b)%Z));
    destruct (pos_div_eucl_sizes a (Z.pos b) eq_refl) as (Hq0 & Hr0 & Hq & Hr);
    destruct (Z.pos_div_eucl a (Z.pos b)) as [q r]; cbn [fst snd size_nat] in *;
    pose proof (T_opp_le q); pose proof (T_opp_le r); pose proof (T_opp_le (q + 1));
    pose proof (T_add_le q 1); pose proof (T_add_le (Z.pos b) r);
    pose proof (T_add_le (Z.neg b) r); pose proof (T_sub_le (Z.pos b) r);
    destruct r; cbn [size_nat Pos.size_nat] in *; lia.
Qed.

Lemma T_div_le (a b : Z) :
  T_div a b <= 16 * (size_nat a + 1) * (size_nat a + size_nat b + 2) + 1.
Proof.
  pose proof (T_div_eucl_le a b). time_unfold T_div. lia.
Qed.

Lemma T_modulo_le (a b : Z) :
  T_modulo a b <= 16 * (size_nat a + 1) * (size_nat a + size_nat b + 2) + 1.
Proof.
  pose proof (T_div_eucl_le a b). time_unfold T_modulo. lia.
Qed.

(** [Z.gcd] runs [Pos.gcd] on the absolute values, so it is quadratic. *)
Lemma T_gcd_le (a b : Z) :
  T_gcd a b <= (size_nat a + size_nat b + 2) * (2 * (size_nat a + size_nat b) + 3) + 2.
Proof.
  destruct a as [| a | a], b as [| b | b]; time_unfold T_gcd; time_pose; cbn [size_nat] in *;
    try pose proof (Pos.T_gcd_le a b); lia.
Qed.

End Z.
