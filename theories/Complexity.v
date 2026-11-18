(** * Complexity bounds

    The bounds 𝑂, Ω and Θ on time functions, each with a notation.
    - A bound relates a time function [T], a measure [g] and a precondition [P] on one input
      [x], the tuple of all the arguments.  For example,

        T ∈ 𝑂(g) for x | P   means   exists c, forall x, P x -> T x <= c * (g x + 1)

    - The constant [c] comes first, so it is the same for all inputs.
    - The [+ 1] lets a constant time be in 𝑂 of a measure that can be 0, such as the length
      of a list.
    - Times and measures have type [N].
    - The bounds are [bigO] (𝑂), [bigOmega] (Ω, a lower bound on every input), [bigTheta] (Θ,
      both), [bigOmega_worst] (Ω in the worst case: reached on inputs of every size), [tight]
      (𝑂 together with Ω in the worst case) and [bigO_amortised] (𝑂 for the time plus the
      change of a potential).
    - The module [ComplexityNotations] writes each of them in the form above.

    For example, [T_length l ∈ Θ(N.of_nat (length l)) for l] holds with the constant 1,
    because [T_length l = N.of_nat (length l) + 1].

    Builds on: Stdlib Lia NArith, Amortised *)

From Stdlib Require Import Lia NArith.
From Argent Require Import Amortised.

Local Open Scope N_scope.

(** * Definitions *)

(** [T x] is at most [c * (g x + 1)] for every input [x] that satisfies [P], with one constant
    [c] for all of them. *)
Definition bigO {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  exists c, forall x, P x -> T x <= c * (g x + 1).

(** [g x] is at most [c * (T x + 1)] for every input [x] that satisfies [P]: up to the
    constant, [T] is at least [g] on every such input. *)
Definition bigOmega {X} (P : X -> Prop) (g T : X -> N) : Prop := bigO P T g.

(** [T] is in 𝑂(g) and in Ω(g) on the inputs that satisfy [P]. *)
Definition bigTheta {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  bigO P g T /\ bigOmega P g T.

(** For every size [n], some input [x] that satisfies [P] and has [g x >= n] takes time at
    least [g x], up to the constant: [g x <= c * T x]. *)
Definition bigOmega_worst {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.

(** [T] is in 𝑂(g) on [P], and in Ω(g) in the worst case: the upper bound is reached on
    inputs of every size. *)
Definition tight {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  bigO P g T /\ exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.

(** The time [T x] plus the potential [after x] that the operation leaves is at most a
    constant multiple of [g x + 1] plus the potential [before x] that it found. *)
Definition bigO_amortised {X} (P : X -> Prop) (g T before after : X -> N) : Prop :=
  exists c, forall x, P x -> T x + after x <= c * (g x + 1) + before x.

(** * Notation *)

(** A bound reads [T ∈ 𝑂(g) for x | P].  The pattern [x], a name or a tuple such as [(p, m)],
    binds the variables of the time [T], the measure [g] and the precondition [P].  Without
    [| P], the precondition is [True].  The time, the measure and the potentials are read in
    [N_scope].  The letter is the italic 𝑂 (U+1D442), so that [O], the zero of [nat], keeps
    parsing as before. *)
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

(** * Upper bounds *)

(** To prove [bigO], give the constant [c] and show [T x <= c * g x + c] on every input. *)
Lemma bigO_intro {X} (P : X -> Prop) (g T : X -> N) c :
  (forall x, P x -> T x <= c * g x + c) -> bigO P g T.
Proof.
  intros Hle. exists c. intros x Hx. specialize (Hle x Hx). lia.
Qed.

(** A smaller time stays in 𝑂(g). *)
Lemma bigO_le {X} (P : X -> Prop) (g T T2 : X -> N) :
  bigO P g T -> (forall x, P x -> T2 x <= T x) -> bigO P g T2.
Proof.
  intros [c Hc] Hle. exists c. intros x Hx. specialize (Hc x Hx). specialize (Hle x Hx). lia.
Qed.

(** A time in 𝑂 of a measure is in 𝑂 of every larger measure. *)
Lemma bigO_mono {X} (P : X -> Prop) (g g2 T : X -> N) :
  bigO P g T -> (forall x, P x -> g x <= g2 x) -> bigO P g2 T.
Proof.
  intros [c Hc] Hle. exists c. intros x Hx. specialize (Hc x Hx). specialize (Hle x Hx). nia.
Qed.

(** The sum of two times is in 𝑂 of the sum of their measures. *)
Lemma bigO_add {X} (P : X -> Prop) (g1 g2 T1 T2 : X -> N) :
  bigO P g1 T1 -> bigO P g2 T2 ->
  bigO P (fun x => g1 x + g2 x) (fun x => T1 x + T2 x).
Proof.
  intros [c1 H1] [c2 H2]. exists (c1 + c2). intros x Hx.
  specialize (H1 x Hx). specialize (H2 x Hx). nia.
Qed.

(** 𝑂 is transitive: when [h] is in 𝑂(g) and [T] is in 𝑂(h), [T] is in 𝑂(g). *)
Lemma bigO_trans {X} (P : X -> Prop) (g h T : X -> N) :
  bigO P g h -> bigO P h T -> bigO P g T.
Proof.
  intros [c1 H1] [c2 H2]. exists (c2 * c1 + c2). intros x Hx.
  specialize (H1 x Hx). specialize (H2 x Hx). nia.
Qed.

(** A bound on inputs of type [Y] gives a bound on inputs of type [X] through any map
    [f : X -> Y], such as a projection of a tuple of arguments. *)
Lemma bigO_comp {X Y} (P : Y -> Prop) (f : X -> Y) (g T : Y -> N) :
  bigO P g T -> bigO (fun x => P (f x)) (fun x => g (f x)) (fun x => T (f x)).
Proof.
  intros [c Hc]. exists c. intros x Hx. exact (Hc (f x) Hx).
Qed.

(** * Domains *)

(** A bound on the inputs that satisfy [P] is the same as a bound on the subset type
    [{x | P x}]. *)
Lemma bigO_subset {X} (P : X -> Prop) (g T : X -> N) :
  bigO P g T <->
  bigO (X := {x | P x}) (fun _ => True) (fun x => g (proj1_sig x)) (fun x => T (proj1_sig x)).
Proof.
  split.
  - intros [c Hc]. exists c. intros [x Hx] _. exact (Hc x Hx).
  - intros [c Hc]. exists c. intros x Hx. exact (Hc (exist _ x Hx) I).
Qed.

(** * Lower bounds *)

(** To prove [bigOmega], give the constant [c] and show [g x <= c * T x + c] on every input. *)
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

(** The lower-bound form of [bigO_add]. *)
Lemma bigOmega_add {X} (P : X -> Prop) (g1 g2 T1 T2 : X -> N) :
  bigOmega P g1 T1 -> bigOmega P g2 T2 ->
  bigOmega P (fun x => g1 x + g2 x) (fun x => T1 x + T2 x).
Proof.
  exact (bigO_add P T1 T2 g1 g2).
Qed.

(** The lower-bound form of [bigO_trans]. *)
Lemma bigOmega_trans {X} (P : X -> Prop) (g h T : X -> N) :
  bigOmega P g h -> bigOmega P h T -> bigOmega P g T.
Proof.
  intros Hgh Hht. exact (bigO_trans P T h g Hht Hgh).
Qed.

(** The lower-bound form of [bigO_comp]. *)
Lemma bigOmega_comp {X Y} (P : Y -> Prop) (f : X -> Y) (g T : Y -> N) :
  bigOmega P g T -> bigOmega (fun x => P (f x)) (fun x => g (f x)) (fun x => T (f x)).
Proof.
  exact (bigO_comp P f T g).
Qed.

(** * Tight bounds *)

(** Θ is 𝑂 together with Ω. *)
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

(** Θ is symmetric: the time and the measure can swap places. *)
Lemma bigTheta_sym {X} (P : X -> Prop) (g T : X -> N) :
  bigTheta P g T -> bigTheta P T g.
Proof.
  intros [Hup Hlow]. split; assumption.
Qed.

(** The Θ form of [bigO_add]. *)
Lemma bigTheta_add {X} (P : X -> Prop) (g1 g2 T1 T2 : X -> N) :
  bigTheta P g1 T1 -> bigTheta P g2 T2 ->
  bigTheta P (fun x => g1 x + g2 x) (fun x => T1 x + T2 x).
Proof.
  intros [Hup1 Hlow1] [Hup2 Hlow2]. split.
  - exact (bigO_add P g1 g2 T1 T2 Hup1 Hup2).
  - exact (bigOmega_add P g1 g2 T1 T2 Hlow1 Hlow2).
Qed.

(** The Θ form of [bigO_trans]. *)
Lemma bigTheta_trans {X} (P : X -> Prop) (g h T : X -> N) :
  bigTheta P g h -> bigTheta P h T -> bigTheta P g T.
Proof.
  intros [Hgh Hhg] [Hht Hth]. split.
  - exact (bigO_trans P g h T Hgh Hht).
  - exact (bigOmega_trans P g h T Hhg Hth).
Qed.

(** The Θ form of [bigO_comp]. *)
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

(** To prove [bigOmega_worst], give for every size [n] an input [w n] that satisfies [P] and
    has [g (w n) >= n], and show [g (w n) <= c * T (w n)]. *)
Lemma bigOmega_worst_intro {X} (P : X -> Prop) (g T : X -> N) (c : N) (w : N -> X) :
  (forall n, P (w n)) -> (forall n, n <= g (w n)) -> (forall n, g (w n) <= c * T (w n)) ->
  bigOmega_worst P g T.
Proof.
  intros HP Hsize Hlow. exists c. intros n. exists (w n). auto.
Qed.

(** To prove [tight], give the upper bound, and inputs [w n] of every size as for
    [bigOmega_worst_intro]. *)
Lemma tight_intro {X} (P : X -> Prop) (g T : X -> N) (c : N) (w : N -> X) :
  bigO P g T ->
  (forall n, P (w n)) -> (forall n, n <= g (w n)) -> (forall n, g (w n) <= c * T (w n)) ->
  tight P g T.
Proof.
  intros Hupper HP Hsize Hlower. split; [exact Hupper |].
  exists c. intros n. exists (w n). auto.
Qed.

(** A lower bound on every input gives the worst-case lower bound, when every input takes at
    least one step and there are inputs of every size. *)
Lemma bigOmega_worst_of_bigOmega {X} (P : X -> Prop) (g T : X -> N) :
  bigOmega P g T -> (forall x, P x -> 1 <= T x) -> (forall n, exists x, P x /\ n <= g x) ->
  bigOmega_worst P g T.
Proof.
  intros [c Hc] Hpos Hsize. exists (2 * c). intros n.
  destruct (Hsize n) as [x [Hx Hn]]. exists x. specialize (Hc x Hx).
  specialize (Hpos x Hx). repeat split; [assumption | assumption | nia].
Qed.

(** Θ gives Θ in the worst case under the same two conditions. *)
Lemma tight_of_bigTheta {X} (P : X -> Prop) (g T : X -> N) :
  bigTheta P g T -> (forall x, P x -> 1 <= T x) -> (forall n, exists x, P x /\ n <= g x) ->
  tight P g T.
Proof.
  intros [Hup Hlow] Hpos Hsize. split; [exact Hup |].
  exact (bigOmega_worst_of_bigOmega P g T Hlow Hpos Hsize).
Qed.

(** * Amortised bounds *)

(** To prove [bigO_amortised], give the constant [c] and show
    [T x + after x <= c * g x + c + before x] on every input. *)
Lemma bigO_amortised_intro {X} (P : X -> Prop) (g T before after : X -> N) c :
  (forall x, P x -> T x + after x <= c * g x + c + before x) ->
  bigO_amortised P g T before after.
Proof.
  intros Hle. exists c. intros x Hx. specialize (Hle x Hx). lia.
Qed.

(** An amortised bound is the same as an upper bound on [T x + after x - before x], the time
    plus the change of the potential, where the subtraction stops at 0. *)
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

(** When the operations [op] keep the invariant [Inv] and meet an amortised bound with the
    potential [Phi], a sequence of operations costs at most [c * (g o s + 1)] per operation, plus
    the potential of its first state, for one constant [c]. *)
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
