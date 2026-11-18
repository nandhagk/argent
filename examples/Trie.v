(** * Binary tries over positive keys

    A binary trie maps keys of type [positive] to values.
    - [get], [set] and [remove] read the key one bit at a time, from the lowest bit: [xO q]
      goes left, [xI q] goes right, [xH] stops.
    - Each operation takes time linear in the bit length of the key ([T_get_le], [T_set_le],
      [T_remove_le]).
    - On a trie that holds the key, [get] reads every bit ([T_get_ge]).  So in the worst case
      [get] takes time Θ of the bit length ([get_worst_complexity]).

    For example, [get 6 m] reads [6 = 1~1~0] from the right: left, right, stop.  It visits at
    most three nodes, so [T_get 6 m <= 3].

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

(** [node] builds a node, except that a node with no value and two empty children becomes a
    leaf.  [remove] uses it so that the trie never keeps empty branches. *)
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

(** The derived time functions follow the same recursion.  [Print T_get] shows:

      T_get =
      fix T_get (A : Type) (p : positive) (m : t A) {struct p} : N :=
        (1 +
         match m with
         | Leaf => 0
         | Node l _ r =>
             match p with
             | q~1%positive => T_get A q r
             | q~0%positive => T_get A q l
             | 1%positive => 0
             end
         end)%N

    [T_node] is the constant 1, and [T_remove] pays [T_node] once per node that it visits. *)
TimeFun get set node remove.

(** * What the operations do *)

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

(** * Upper bounds *)

(** The three proofs below share one shape: induction on the key, for every trie, then a case
    on the trie.  In each case [time_step] unfolds the time function once, and the induction
    hypothesis pays for the call on the rest of the key. *)

(** [get] visits at most one node per bit of the key. *)
Theorem T_get_le {A : Type} (p : positive) (m : t A) :
  T_get p m <= N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.

(** [set] visits one node per bit of the key. *)
Theorem T_set_le {A : Type} (p : positive) (v : A) (m : t A) :
  T_set p v m <= N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.

(** [remove] visits at most one node per bit of the key, and calls [node] once at each. *)
Theorem T_remove_le {A : Type} (p : positive) (m : t A) :
  T_remove p m <= 2 * N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.

(** * A lower bound *)

(** On a trie that holds the key, [get] visits one node per bit of the key: [set] has built a
    node for every bit, so [get] never stops early at a leaf. *)
Theorem T_get_ge {A : Type} (p : positive) (v : A) (m : t A) :
  N.of_nat (Pos.size_nat p) <= T_get p (set p v m).
Proof.
  revert m. induction p as [q IH | q IH |]; intros [| l o r];
    cbn [set]; time_unfold @T_get; cbn [Pos.size_nat].
  - (* Key [q~1] in a leaf: [set] builds a right child that holds [q]. *)
    pose proof (IH Leaf) as Hq. lia.
  - (* Key [q~1] in a node: [set] puts [q] into the right child [r]. *)
    pose proof (IH r) as Hq. lia.
  - (* Key [q~0] in a leaf: [set] builds a left child that holds [q]. *)
    pose proof (IH Leaf) as Hq. lia.
  - (* Key [q~0] in a node: [set] puts [q] into the left child [l]. *)
    pose proof (IH l) as Hq. lia.
  - (* Key [1] in a leaf: one bit and one step. *)
    lia.
  - (* Key [1] in a node: one bit and one step. *)
    lia.
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

(** [ones n] is the key [1~1~...~1] with [n] ones after the leading 1, so it has [n + 1]
    bits. *)
Fixpoint ones (n : nat) : positive :=
  match n with
  | O => xH
  | S k => xI (ones k)
  end.

Lemma size_nat_ones (n : nat) : Pos.size_nat (ones n) = S n.
Proof.
  induction n as [| n IH]; cbn; congruence.
Qed.

(** In the worst case, [get] takes time Θ of the bit length of the key.  The upper bound is
    [get_complexity].  For the lower bound, [tight_intro] asks for an input of every size [n]
    on which [get] is slow: the key [ones n] in a trie that holds it. *)
Theorem get_worst_complexity {A : Type} (a : A) :
  T_get (A := A) p m ∈ Θ_worst(N.of_nat (Pos.size_nat p)) for (p, m).
Proof.
  apply tight_intro with (c := 1)
    (w := fun n => (ones (N.to_nat n), set (ones (N.to_nat n)) a Leaf)).
  - (* The upper bound. *)
    exact get_complexity.
  - (* Every input satisfies the precondition, which is [True]. *)
    intros n. exact I.
  - (* The key [ones n] has at least [n] bits. *)
    intros n. cbn beta iota. rewrite size_nat_ones. lia.
  - (* On that input, [get] takes at least one step per bit, by [T_get_ge]. *)
    intros n. cbn beta iota. pose proof (T_get_ge (ones (N.to_nat n)) a Leaf) as Hhit. lia.
Qed.
