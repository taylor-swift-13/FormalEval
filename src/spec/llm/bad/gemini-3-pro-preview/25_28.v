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

Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d [k Hk].
    destruct d as [| [| [| ]]]; simpl in Hk.
    + discriminate.
    + left. reflexivity.
    + right. reflexivity.
    + lia.
Qed.

Lemma prime_3 : is_prime 3.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d [k Hk].
    destruct d as [| [| [| [| ]]]]; simpl in Hk.
    + discriminate.
    + left. reflexivity.
    + lia.
    + right. reflexivity.
    + lia.
Qed.

Lemma prime_11 : is_prime 11.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d [k Hk].
    destruct d as [| [| [| [| [| [| [| [| [| [| [| [| ]]]]]]]]]]]]; simpl in Hk.
    + discriminate.
    + left. reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + right. reflexivity.
    + lia.
Qed.

Example test_factorize_132 : factorize_spec 132 [2; 2; 3; 11].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + apply Forall_cons. apply prime_2.
      apply Forall_cons. apply prime_2.
      apply Forall_cons. apply prime_3.
      apply Forall_cons. apply prime_11.
      apply Forall_nil.
    + repeat constructor; simpl; try lia.
Qed.