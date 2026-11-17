(** * Complexity bounds

    This file completes the bounds of BigO and writes all of them in one notation.  Each bound
    relates a time function [T] and a measure [g] on the inputs that satisfy a precondition
    [P], with one constant for all those inputs.  [bigO] is the upper bound 𝑂, [bigOmega] the
    lower bound Ω on every input, [bigTheta] both, [bigOmega_worst] a lower bound that inputs
    of every size reach, [tight] the upper bound with that worst-case lower bound, and
    [bigO_amortised] an upper bound on the time plus the change of a potential.  The module
    [ComplexityNotations] writes a bound as [T x ∈ 𝑂(g x) for x | P x], where [x] is a name
    or a tuple pattern and [| P x] may be left out.  A bound on the inputs that satisfy [P] is
    a bound on the subset type [{x | P x}] ([bigO_subset]).

    For example, [T_length l ∈ Θ(N.of_nat (length l)) for l] holds with the constant 1,
    because [T_length l = N.of_nat (length l) + 1].

    Builds on: BigO Amortised *)

From Stdlib Require Import Lia NArith.
From Argent Require Export BigO.
From Argent Require Import Amortised.

Local Open Scope N_scope.

(** * Definitions *)

(** [g] is at most a constant multiple of [T + 1] on the inputs that satisfy [P]. *)
Definition bigOmega {X} (P : X -> Prop) (g T : X -> N) : Prop := bigO P T g.

(** [T] is in 𝑂(g) and in Ω(g) on the inputs that satisfy [P]. *)
Definition bigTheta {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  bigO P g T /\ bigOmega P g T.

(** Inputs of every size satisfy [P] and take time at least [g] over a constant. *)
Definition bigOmega_worst {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.

(** The time [T x] plus the potential [after x] that the operation leaves is at most a
    constant multiple of [g x + 1] plus the potential [before x] that it found. *)
Definition bigO_amortised {X} (P : X -> Prop) (g T before after : X -> N) : Prop :=
  exists c, forall x, P x -> T x + after x <= c * (g x + 1) + before x.

(** * Notation *)

(** A bound reads [T ∈ 𝑂(g) for x | P], where the pattern [x] binds the variables of the time
    [T], the measure [g] and the precondition [P].  Without [| P] the precondition is [True].
    The time, the measure and the potentials are read in [N_scope]. *)
Module ComplexityNotations.

  Notation "T ∈ 𝑂( g ) 'for' x | P" := (bigO (fun x => P) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, P at level 200, no associativity,
     format "'[hv  ' T  ∈  𝑂( g )  '/' for  x  |  P ']'").
  Notation "T ∈ 𝑂( g ) 'for' x" := (bigO (fun _ => True) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, no associativity,
     format "'[hv  ' T  ∈  𝑂( g )  '/' for  x ']'").

  Notation "T ∈ Ω( g ) 'for' x | P" := (bigOmega (fun x => P) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, P at level 200, no associativity,
     format "'[hv  ' T  ∈  Ω( g )  '/' for  x  |  P ']'").
  Notation "T ∈ Ω( g ) 'for' x" := (bigOmega (fun _ => True) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, no associativity,
     format "'[hv  ' T  ∈  Ω( g )  '/' for  x ']'").

  Notation "T ∈ Θ( g ) 'for' x | P" := (bigTheta (fun x => P) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, P at level 200, no associativity,
     format "'[hv  ' T  ∈  Θ( g )  '/' for  x  |  P ']'").
  Notation "T ∈ Θ( g ) 'for' x" := (bigTheta (fun _ => True) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, no associativity,
     format "'[hv  ' T  ∈  Θ( g )  '/' for  x ']'").

  Notation "T ∈ Ω_worst( g ) 'for' x | P" :=
    (bigOmega_worst (fun x => P) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, P at level 200, no associativity,
     format "'[hv  ' T  ∈  Ω_worst( g )  '/' for  x  |  P ']'").
  Notation "T ∈ Ω_worst( g ) 'for' x" :=
    (bigOmega_worst (fun _ => True) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, no associativity,
     format "'[hv  ' T  ∈  Ω_worst( g )  '/' for  x ']'").

  Notation "T ∈ Θ_worst( g ) 'for' x | P" :=
    (tight (fun x => P) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, P at level 200, no associativity,
     format "'[hv  ' T  ∈  Θ_worst( g )  '/' for  x  |  P ']'").
  Notation "T ∈ Θ_worst( g ) 'for' x" :=
    (tight (fun _ => True) (fun x => g%N) (fun x => T%N))
    (at level 70, x pattern, g at level 200, no associativity,
     format "'[hv  ' T  ∈  Θ_worst( g )  '/' for  x ']'").

  Notation "T ∈ 𝑂( g ) 'amortised' a ↦ b 'for' x | P" :=
    (bigO_amortised (fun x => P) (fun x => g%N) (fun x => T%N)
       (fun x => a%N) (fun x => b%N))
    (at level 70, x pattern, g at level 200, a at level 69, b at level 69, P at level 200,
     no associativity,
     format "'[hv  ' T  ∈  𝑂( g )  '/' amortised  a  ↦  b  '/' for  x  |  P ']'").
  Notation "T ∈ 𝑂( g ) 'amortised' a ↦ b 'for' x" :=
    (bigO_amortised (fun _ => True) (fun x => g%N) (fun x => T%N)
       (fun x => a%N) (fun x => b%N))
    (at level 70, x pattern, g at level 200, a at level 69, b at level 69, no associativity,
     format "'[hv  ' T  ∈  𝑂( g )  '/' amortised  a  ↦  b  '/' for  x ']'").

End ComplexityNotations.

Import ComplexityNotations.

(** * Domains *)

(** A bound on the inputs that satisfy [P] is a bound on the subset type [{x | P x}]. *)
Lemma bigO_subset {X} (P : X -> Prop) (g T : X -> N) :
  bigO P g T <->
  bigO (X := {x | P x}) (fun _ => True) (fun x => g (proj1_sig x)) (fun x => T (proj1_sig x)).
Proof.
  split.
  - intros [c Hc]. exists c. intros [x Hx] _. exact (Hc x Hx).
  - intros [c Hc]. exists c. intros x Hx. exact (Hc (exist _ x Hx) I).
Qed.

(** * Lower bounds *)

Lemma bigOmega_intro {X} (P : X -> Prop) (g T : X -> N) c :
  (forall x, P x -> g x <= c * T x + c) -> bigOmega P g T.
Proof.
  exact (bigO_intro P T g c).
Qed.

(** A larger time keeps a lower bound. *)
Lemma bigOmega_le {X} (P : X -> Prop) (g T T2 : X -> N) :
  bigOmega P g T -> (forall x, P x -> T x <= T2 x) -> bigOmega P g T2.
Proof.
  intros Hlow Hle. exact (bigO_mono P T T2 g Hlow Hle).
Qed.

(** A smaller measure keeps a lower bound. *)
Lemma bigOmega_mono {X} (P : X -> Prop) (g g2 T : X -> N) :
  bigOmega P g T -> (forall x, P x -> g2 x <= g x) -> bigOmega P g2 T.
Proof.
  intros Hlow Hle. exact (bigO_le P T g g2 Hlow Hle).
Qed.

Lemma bigOmega_add {X} (P : X -> Prop) (g1 g2 T1 T2 : X -> N) :
  bigOmega P g1 T1 -> bigOmega P g2 T2 ->
  bigOmega P (fun x => g1 x + g2 x) (fun x => T1 x + T2 x).
Proof.
  exact (bigO_add P T1 T2 g1 g2).
Qed.

Lemma bigOmega_trans {X} (P : X -> Prop) (g h T : X -> N) :
  bigOmega P g h -> bigOmega P h T -> bigOmega P g T.
Proof.
  intros Hgh Hht. exact (bigO_trans P T h g Hht Hgh).
Qed.

Lemma bigOmega_comp {X Y} (P : Y -> Prop) (f : X -> Y) (g T : Y -> N) :
  bigOmega P g T -> bigOmega (fun x => P (f x)) (fun x => g (f x)) (fun x => T (f x)).
Proof.
  exact (bigO_comp P f T g).
Qed.

(** * Tight bounds *)

Lemma bigTheta_intro {X} (P : X -> Prop) (g T : X -> N) :
  bigO P g T -> bigOmega P g T -> bigTheta P g T.
Proof.
  split; assumption.
Qed.

(** A time that equals the measure plus a constant is in Θ of the measure. *)
Lemma bigTheta_shift {X} (P : X -> Prop) (g T : X -> N) (k : N) :
  (forall x, P x -> T x = g x + k) -> bigTheta P g T.
Proof.
  intros Heq. split.
  - exists (k + 1). intros x Hx. rewrite (Heq x Hx). nia.
  - exists 1. intros x Hx. rewrite (Heq x Hx). lia.
Qed.

Lemma bigTheta_sym {X} (P : X -> Prop) (g T : X -> N) :
  bigTheta P g T -> bigTheta P T g.
Proof.
  intros [Hup Hlow]. split; assumption.
Qed.

Lemma bigTheta_add {X} (P : X -> Prop) (g1 g2 T1 T2 : X -> N) :
  bigTheta P g1 T1 -> bigTheta P g2 T2 ->
  bigTheta P (fun x => g1 x + g2 x) (fun x => T1 x + T2 x).
Proof.
  intros [Hup1 Hlow1] [Hup2 Hlow2]. split.
  - exact (bigO_add P g1 g2 T1 T2 Hup1 Hup2).
  - exact (bigOmega_add P g1 g2 T1 T2 Hlow1 Hlow2).
Qed.

Lemma bigTheta_trans {X} (P : X -> Prop) (g h T : X -> N) :
  bigTheta P g h -> bigTheta P h T -> bigTheta P g T.
Proof.
  intros [Hgh Hhg] [Hht Hth]. split.
  - exact (bigO_trans P g h T Hgh Hht).
  - exact (bigOmega_trans P g h T Hhg Hth).
Qed.

Lemma bigTheta_comp {X Y} (P : Y -> Prop) (f : X -> Y) (g T : Y -> N) :
  bigTheta P g T -> bigTheta (fun x => P (f x)) (fun x => g (f x)) (fun x => T (f x)).
Proof.
  intros [Hup Hlow]. split.
  - exact (bigO_comp P f g T Hup).
  - exact (bigOmega_comp P f g T Hlow).
Qed.

(** * Worst-case bounds *)

(** [tight] is the upper bound with the worst-case lower bound. *)
Lemma tight_iff {X} (P : X -> Prop) (g T : X -> N) :
  tight P g T <-> bigO P g T /\ bigOmega_worst P g T.
Proof.
  reflexivity.
Qed.

(** Witnesses [w n] of every size [n] give the worst-case lower bound. *)
Lemma bigOmega_worst_intro {X} (P : X -> Prop) (g T : X -> N) (c : N) (w : N -> X) :
  (forall n, P (w n)) -> (forall n, n <= g (w n)) -> (forall n, g (w n) <= c * T (w n)) ->
  bigOmega_worst P g T.
Proof.
  intros HP Hsize Hlow. exists c. intros n. exists (w n). auto.
Qed.

(** A pointwise lower bound on a time of at least 1 gives the worst-case lower bound on a
    domain with inputs of every size. *)
Lemma bigOmega_worst_of_bigOmega {X} (P : X -> Prop) (g T : X -> N) :
  bigOmega P g T -> (forall x, P x -> 1 <= T x) -> (forall n, exists x, P x /\ n <= g x) ->
  bigOmega_worst P g T.
Proof.
  intros [c Hc] Hpos Hsize. exists (2 * c). intros n.
  destruct (Hsize n) as [x [Hx Hn]]. exists x. specialize (Hc x Hx).
  specialize (Hpos x Hx). repeat split; [assumption | assumption | nia].
Qed.

Lemma tight_of_bigTheta {X} (P : X -> Prop) (g T : X -> N) :
  bigTheta P g T -> (forall x, P x -> 1 <= T x) -> (forall n, exists x, P x /\ n <= g x) ->
  tight P g T.
Proof.
  intros [Hup Hlow] Hpos Hsize. split; [exact Hup |].
  exact (bigOmega_worst_of_bigOmega P g T Hlow Hpos Hsize).
Qed.

(** * Amortised bounds *)

Lemma bigO_amortised_intro {X} (P : X -> Prop) (g T before after : X -> N) c :
  (forall x, P x -> T x + after x <= c * g x + c + before x) ->
  bigO_amortised P g T before after.
Proof.
  intros Hle. exists c. intros x Hx. specialize (Hle x Hx). lia.
Qed.

(** The amortised bound is the upper bound of the time plus the rise of the potential. *)
Lemma bigO_amortised_sub {X} (P : X -> Prop) (g T before after : X -> N) :
  bigO_amortised P g T before after <->
  bigO P g (fun x => T x + after x - before x).
Proof.
  split.
  - intros [c Hc]. exists c. intros x Hx. specialize (Hc x Hx). lia.
  - intros [c Hc]. exists c. intros x Hx. specialize (Hc x Hx). lia.
Qed.

(** A worst-case bound with a potential that never rises is an amortised bound. *)
Lemma bigO_amortised_of_bigO {X} (P : X -> Prop) (g T before after : X -> N) :
  bigO P g T -> (forall x, P x -> after x <= before x) -> bigO_amortised P g T before after.
Proof.
  intros [c Hc] Hfall. exists c. intros x Hx. specialize (Hc x Hx).
  specialize (Hfall x Hx). lia.
Qed.

(** When the operations [op] keep the invariant [Inv] and meet the amortised bound with the
    potential [Phi], a sequence of operations costs at most [c * (g o s + 1)] per operation
    plus the potential of its first state, for one constant [c]. *)
Theorem bigO_amortised_run {S O} (op : O -> S -> S) (T g : O -> S -> N) (Phi : S -> N)
    (Inv : S -> Prop) :
  (forall o s, Inv s -> Inv (op o s)) ->
  (T o s ∈ 𝑂(g o s) amortised Phi s ↦ Phi (op o s) for (o, s) | Inv s) ->
  exists c, forall os s, Inv s ->
    total op T os s <= budget op (fun o s => c * (g o s + 1)) os s + Phi s.
Proof.
  intros Hinv [c Hc]. exists c. intros os s Hs.
  assert (Hstep : amortised op T (fun o s => c * (g o s + 1)) Phi Inv).
  { intros o s1 Hs1. split; [exact (Hinv o s1 Hs1) |].
    exact (Hc (o, s1) Hs1). }
  pose proof (amortised_run op T (fun o s => c * (g o s + 1)) Phi Inv Hstep os s Hs) as Hrun.
  lia.
Qed.
