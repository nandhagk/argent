(** * Maps over abstract keys

    Code that is generic over a module gets its bounds from the module's signature.  So a
    signature here has two layers.  The functional layer declares the operations and their
    laws, as usual.  The time layer declares, for each operation, its time function, a named
    constant, and a contract that bounds the time function using that constant.  Every
    implementation proves the contracts for its own constant.  A client functor can only use
    the contracts, so its bounds hold for every implementation.

    [TrieMap] implements [MAP] on the trie of Trie.v, for any [KEY].  [SumValues] is a client
    functor over [MAP].

    For example, [NatSum.sum_values [0; 2; 5] m] adds the values that [m] holds at the keys 0,
    2 and 5.  Its time is linear in the lengths of the encoded keys and in the values added.

    Builds on: Time Tactics Std Trie *)

From Stdlib Require Import List PArith NArith Lia.
From Argent Require Import Time Tactics Std.
From Argent.Examples Require Trie.
Import List.ListNotations.

(** * Signatures *)

(** A key type with an injective encoding into [positive]. *)
Module Type KEY.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter encode_inj : forall a b, encode a = encode b -> a = b.
  (** The time layer: [encode k] takes at most [c_encode * (b + 1)] steps, where [b] is the
      bit length of [encode k]. *)
  Parameter T_encode : t -> N.
  Parameter c_encode : N.
  Parameter T_encode_le :
    forall k, (T_encode k <= c_encode * (N.of_nat (Pos.size_nat (encode k)) + 1))%N.
End KEY.

(** Finite maps from [K.t] to values. *)
Module Type MAP.
  Declare Module K : KEY.
  Parameter t : Type -> Type.
  Parameter empty : forall {A : Type}, t A.
  Parameter get : forall {A : Type}, K.t -> t A -> option A.
  Parameter set : forall {A : Type}, K.t -> A -> t A -> t A.
  Parameter get_empty : forall A k, get k (@empty A) = None.
  Parameter get_set_same : forall A k (v : A) m, get k (set k v m) = Some v.
  Parameter get_set_other : forall A k k' (v : A) m, k <> k' -> get k' (set k v m) = get k' m.
  (** The time layer: [get k m] and [set k v m] take at most [c_map * (b + 1)] steps, where
      [b] is the bit length of [K.encode k].  [T_get] and [T_set] are the names that [TimeFun]
      looks for, so a client's [TimeFun] charges a call of [M.get] with [M.T_get]. *)
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

  (** [T_get k m = 1 + K.T_encode k + Trie.T_get (K.encode k) m]: one step for the call, the
      encoding of the key, and the trie lookup.  [T_set] has the same shape. *)
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

  (** The encoding pays [K.c_encode] per bit, and the trie pays 1 per bit, plus 1 for the
      call of [get] or [set]. *)
  Definition c_map : N := (K.c_encode + 2)%N.

  (** [time_step] adds the contract [K.T_encode_le] and the trie bound [Trie.T_get_le], and
      the arithmetic gives the constant [c_map]. *)
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

  (** The key [n] is encoded as [2 ^ n].  Its bit length, [n + 1], is the size of [n] in
      unary, so the encoding takes one step per bit. *)
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

  (** [M.get] has no body here, because [M] is a functor parameter.  [TimeFun] charges a call
      of [M.get] with the time function that the signature declares, [M.T_get]. *)
  TimeFun sum_values.

  (** The total bit length of the encoded keys, each plus one. *)
  Fixpoint key_work (ks : list M.K.t) : nat :=
    match ks with
    | [] => 0
    | k :: r => Pos.size_nat (M.K.encode k) + 1 + key_work r
    end.

  (** The time of [sum_values] is linear in the lengths of the encoded keys and in the values
      added, because addition on [nat] is unary.  The proof uses only the contract
      [M.T_get_le], so it holds for every implementation of [MAP]. *)
  Theorem T_sum_values_le (ks : list M.K.t) (m : M.t nat) :
    (T_sum_values ks m <=
     (M.c_map + 2) * N.of_nat (key_work ks) + N.of_nat (sum_values ks m) + 1)%N.
  Proof.
    (* Per key: one call, the lookup, and an addition when the key is present. *)
    induction ks as [| k r IH]; time_step.
  Qed.

End SumValues.

Module NatSum := SumValues NatMap.

Example nat_sum_runs :
  NatSum.sum_values [0; 2; 5] (NatMap.set 2 10 (NatMap.set 0 1 NatMap.empty)) = 11 :=
  eq_refl.
