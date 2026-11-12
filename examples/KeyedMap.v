(** * Maps over abstract keys

    This file shows the signature convention.  A signature has a functional layer, the
    operations and their laws, and a time layer: a time function per operation, a named
    constant and a contract that bounds the time function by the constant.  [TrieMap] builds a
    map from any [KEY] on the trie of Trie.v and discharges the contracts.  [SumValues] is a
    client functor over an abstract [MAP]; it derives its own time function and proves its
    bound from the contracts of [MAP] alone, so it cannot depend on the costs of a backend.

    For example, [NatSum.sum_values [0; 2] m] adds the values that [m] holds at keys 0 and 2,
    in time linear in the key lengths and in those values.

    Builds on: Time Tactics Std Trie *)

From Stdlib Require Import List PArith NArith Lia.
From Argent Require Import Time Tactics Std.
From Argent.Examples Require Trie.
Import List.ListNotations.

(** * Signatures *)

Module Type KEY.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter encode_inj : forall a b, encode a = encode b -> a = b.
  (* Time layer. *)
  Parameter T_encode : t -> N.
  Parameter c_encode : N.
  Parameter T_encode_le :
    forall k, (T_encode k <= c_encode * (N.of_nat (Pos.size_nat (encode k)) + 1))%N.
End KEY.

Module Type MAP.
  Declare Module K : KEY.
  Parameter t : Type -> Type.
  Parameter empty : forall {A : Type}, t A.
  Parameter get : forall {A : Type}, K.t -> t A -> option A.
  Parameter set : forall {A : Type}, K.t -> A -> t A -> t A.
  Parameter get_empty : forall A k, get k (@empty A) = None.
  Parameter get_set_same : forall A k (v : A) m, get k (set k v m) = Some v.
  Parameter get_set_other : forall A k k' (v : A) m, k <> k' -> get k' (set k v m) = get k' m.
  (* Time layer. *)
  Parameter T_get : forall {A : Type}, K.t -> t A -> N.
  Parameter T_set : forall {A : Type}, K.t -> A -> t A -> N.
  Parameter c_map : N.
  Parameter T_get_le :
    forall A k (m : t A), (T_get k m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
  Parameter T_set_le :
    forall A k (v : A) m,
      (T_set k v m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
End MAP.

(** * A map on tries *)

Module TrieMap (K0 : KEY) <: MAP with Module K := K0.
  Module K := K0.

  Definition t : Type -> Type := Trie.t.

  Definition empty {A : Type} : t A := Trie.Leaf.

  Definition get {A : Type} (k : K.t) (m : t A) : option A := Trie.get (K.encode k) m.

  Definition set {A : Type} (k : K.t) (v : A) (m : t A) : t A := Trie.set (K.encode k) v m.

  TimeFun get set.

  Lemma get_empty A k : get k (@empty A) = None.
  Proof.
    apply Trie.get_leaf.
  Qed.

  Lemma get_set_same A k (v : A) m : get k (set k v m) = Some v.
  Proof.
    apply Trie.get_set_same.
  Qed.

  Lemma get_set_other A k k' (v : A) m : k <> k' -> get k' (set k v m) = get k' m.
  Proof.
    intros Hne. apply Trie.get_set_other. intros Heq. apply Hne, K.encode_inj, Heq.
  Qed.

  Definition c_map : N := (K.c_encode + 2)%N.

  Lemma T_get_le A k (m : t A) :
    (T_get k m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
  Proof.
    unfold c_map. time_step.
  Qed.

  Lemma T_set_le A k (v : A) m :
    (T_set k v m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
  Proof.
    unfold c_map. time_step.
  Qed.
End TrieMap.

(** * Natural-number keys *)

Module NatKey <: KEY.
  Definition t : Type := nat.

  (** The key [n] is encoded as [2 ^ n], whose bit length [n + 1] is the size of [n] in
      unary. *)
  Fixpoint encode (n : t) : positive :=
    match n with
    | 0 => xH
    | S m => xO (encode m)
    end.

  TimeFun encode.

  Lemma encode_inj a b : encode a = encode b -> a = b.
  Proof.
    revert b. induction a as [| a IH]; intros [| b] Heq; cbn in Heq; try discriminate.
    - reflexivity.
    - f_equal. apply IH. congruence.
  Qed.

  Definition c_encode : N := 1%N.

  Lemma T_encode_le k : (T_encode k <= c_encode * (N.of_nat (Pos.size_nat (encode k)) + 1))%N.
  Proof.
    unfold c_encode. induction k as [| k IH]; time_step.
  Qed.
End NatKey.

Module NatMap := TrieMap NatKey.

(** * A client of the signature *)

Module SumValues (M : MAP).

  (** The sum of the values held at the keys [ks]. *)
  Fixpoint sum_values (ks : list M.K.t) (m : M.t nat) : nat :=
    match ks with
    | [] => 0
    | k :: r =>
      match M.get k m with
      | Some v => v + sum_values r m
      | None => sum_values r m
      end
    end.

  TimeFun sum_values.

  (** The total bit length of the encoded keys, each plus one. *)
  Fixpoint key_work (ks : list M.K.t) : nat :=
    match ks with
    | [] => 0
    | k :: r => Pos.size_nat (M.K.encode k) + 1 + key_work r
    end.

  (** The time of [sum_values] is linear in the encoded key lengths and in the values added,
      since addition on [nat] is unary.  The proof uses only the contracts of [MAP]. *)
  Theorem T_sum_values_le (ks : list M.K.t) (m : M.t nat) :
    (T_sum_values ks m <=
     (M.c_map + 2) * N.of_nat (key_work ks) + N.of_nat (sum_values ks m) + 1)%N.
  Proof.
    induction ks as [| k r IH]; time_step.
  Qed.

End SumValues.

Module NatSum := SumValues NatMap.

Example nat_sum_runs :
  NatSum.sum_values [0; 2; 5] (NatMap.set 2 10 (NatMap.set 0 1 NatMap.empty)) = 11 :=
  eq_refl.
