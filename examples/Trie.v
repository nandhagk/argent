(** * Binary tries over positive keys

    This file defines a binary trie keyed by [positive] with [get], [set] and [remove], derives
    their time functions, and proves that each costs at most a constant times the bit length of
    the key.  It also proves a matching lower bound for [get], and it states the complexity of
    each operation in the notation of [Complexity], with Θ in the worst case for [get].

    For example, [get 6 m] follows the bits of [6 = 1~1~0], so it visits at most three nodes and
    [T_get 6 m <= 3].

    Builds on: Time Tactics Complexity Std *)

From Stdlib Require Import PArith NArith Lia.
From Argent Require Import Time Tactics Complexity Std.
Import ComplexityNotations.

Local Open Scope N_scope.

(** * The trie and its operations *)

Inductive t (A : Type) : Type :=
  | Leaf
  | Node (l : t A) (v : option A) (r : t A).

Arguments Leaf {A}.
Arguments Node {A} l v r.

Fixpoint get {A : Type} (p : positive) (m : t A) {struct p} : option A :=
  match m with
  | Leaf => None
  | Node l v r =>
    match p with
    | xH => v
    | xO q => get q l
    | xI q => get q r
    end
  end.

Fixpoint set {A : Type} (p : positive) (v : A) (m : t A) {struct p} : t A :=
  match m with
  | Leaf =>
    match p with
    | xH => Node Leaf (Some v) Leaf
    | xO q => Node (set q v Leaf) None Leaf
    | xI q => Node Leaf None (set q v Leaf)
    end
  | Node l o r =>
    match p with
    | xH => Node l (Some v) r
    | xO q => Node (set q v l) o r
    | xI q => Node l o (set q v r)
    end
  end.

(** A node with no value and two empty children is a leaf, so that removal keeps tries
    canonical. *)
Definition node {A : Type} (l : t A) (o : option A) (r : t A) : t A :=
  match l, o, r with
  | Leaf, None, Leaf => Leaf
  | _, _, _ => Node l o r
  end.

Fixpoint remove {A : Type} (p : positive) (m : t A) {struct p} : t A :=
  match m with
  | Leaf => Leaf
  | Node l o r =>
    match p with
    | xH => node l None r
    | xO q => node (remove q l) o r
    | xI q => node l o (remove q r)
    end
  end.

TimeFun get set node remove.

(** * Functional laws *)

Lemma get_set_same {A : Type} (p : positive) (v : A) (m : t A) : get p (set p v m) = Some v.
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; cbn; auto.
Qed.

Lemma get_leaf {A : Type} (p : positive) : get p (@Leaf A) = None.
Proof.
  destruct p; reflexivity.
Qed.

Lemma get_set_other {A : Type} (p q : positive) (v : A) (m : t A) :
  p <> q -> get q (set p v m) = get q m.
Proof.
  revert q m. induction p as [p IH | p IH |]; intros [q | q |] [| l o r] Hne; cbn;
    rewrite ?get_leaf; try reflexivity; try congruence;
    rewrite IH by congruence; rewrite ?get_leaf; reflexivity.
Qed.

(** * Bounds *)

(** [get] visits at most one node per bit of the key. *)
Theorem T_get_le {A : Type} (p : positive) (m : t A) :
  T_get p m <= N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.

(** [set] visits exactly one node per bit of the key. *)
Theorem T_set_le {A : Type} (p : positive) (v : A) (m : t A) :
  T_set p v m <= N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.

(** [remove] visits at most one node per bit and rebuilds each with [node]. *)
Theorem T_remove_le {A : Type} (p : positive) (m : t A) :
  T_remove p m <= 2 * N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.

(** On a trie that holds the key, [get] visits one node per bit of the key. *)
Theorem T_get_ge {A : Type} (p : positive) (v : A) (m : t A) :
  N.of_nat (Pos.size_nat p) <= T_get p (set p v m).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; cbn [set];
    time_unfold @T_get; cbn [Pos.size_nat]; try pose proof (IH Leaf);
    try pose proof (IH l); try pose proof (IH r); lia.
Qed.

(** * Complexity *)

(** [get] runs in time 𝑂 of the bit length of the key. *)
Theorem get_complexity {A : Type} :
  T_get (A := A) p m ∈ 𝑂(N.of_nat (Pos.size_nat p)) for (p, m).
Proof.
  apply bigO_intro with (c := 1). intros [p m] _. pose proof (T_get_le p m) as Hget. lia.
Qed.

(** [set] runs in time 𝑂 of the bit length of the key. *)
Theorem set_complexity {A : Type} :
  T_set (A := A) p v m ∈ 𝑂(N.of_nat (Pos.size_nat p)) for (p, v, m).
Proof.
  apply bigO_intro with (c := 1). intros [[p v] m] _. pose proof (T_set_le p v m) as Hset.
  lia.
Qed.

(** [remove] runs in time 𝑂 of the bit length of the key. *)
Theorem remove_complexity {A : Type} :
  T_remove (A := A) p m ∈ 𝑂(N.of_nat (Pos.size_nat p)) for (p, m).
Proof.
  apply bigO_intro with (c := 2). intros [p m] _. pose proof (T_remove_le p m) as Hremove.
  lia.
Qed.

(** The key [1~1~...~1] with [n] ones after the leading bit. *)
Fixpoint ones (n : nat) : positive :=
  match n with
  | O => xH
  | S k => xI (ones k)
  end.

Lemma size_nat_ones (n : nat) : Pos.size_nat (ones n) = S n.
Proof.
  induction n as [| n IH]; cbn; congruence.
Qed.

(** In the worst case [get] takes time Θ of the bit length of the key, because on a trie that
    holds the key it reads every bit, and such tries exist for keys of every length. *)
Theorem get_worst_complexity {A : Type} (a : A) :
  T_get (A := A) p m ∈ Θ_worst(N.of_nat (Pos.size_nat p)) for (p, m).
Proof.
  apply tight_intro with (c := 1)
    (w := fun n => (ones (N.to_nat n), set (ones (N.to_nat n)) a Leaf)).
  - exact get_complexity.
  - intros n. exact I.
  - intros n. cbn beta iota. rewrite size_nat_ones. lia.
  - intros n. cbn beta iota. pose proof (T_get_ge (ones (N.to_nat n)) a Leaf) as Hhit. lia.
Qed.
