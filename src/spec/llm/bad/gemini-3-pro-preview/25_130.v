Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Fixpoint check_range (n d : nat) (count : nat) : bool :=
  match count with
  | 0 => true
  | S c => if (n mod d =? 0) then false else check_range n (S d) c
  end.

Definition is_prime_b (n : nat) : bool :=
  if n <=? 1 then false
  else check_range n 2 (n - 2).

Lemma check_range_correct : forall n d c,
  check_range n d c = true ->
  forall k, d <= k < d + c -> n mod k <> 0.
Proof.
  induction c; intros.
  - lia.
  - simpl in H.
    destruct (n mod d =? 0) eqn:E.
    + discriminate.
    + apply Nat.eqb_neq in E.
      assert (k = d \/ d < k < d + S c) by lia.
      destruct H0.
      * subst. assumption.
      * apply IHc; auto. lia.
Qed.

Lemma is_prime_b_correct : forall n, is_prime_b n = true -> is_prime n.
Proof.
  intros n H.
  unfold is_prime_b in H.
  destruct (n <=? 1) eqn:Le.
  - discriminate.
  - apply Nat.leb_nle in Le.
    split; [lia|].
    intros d Hd.
    assert (d = 0 \/ d = 1 \/ 1 < d < n \/ d = n \/ n < d) by lia.
    destruct H0 as [?|[?|[?|[?|?]]]]; try lia; try (left; assumption); try (right; assumption).
    + subst. destruct Hd. simpl in H0. discriminate.
    + apply Nat.mod_divide in Hd; [|lia].
      assert (2 <= d < 2 + (n - 2)) by lia.
      apply (check_range_correct n 2 (n - 2)) in H; auto.
      specialize (H d H0).
      contradiction.
    + apply Nat.divide_pos_le in Hd; lia.
Qed.

Example test_factorize_999987 : factorize_spec 999987 [3; 257; 1297].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor; apply is_prime_b_correct; vm_compute; reflexivity.
    + repeat constructor.
Qed.