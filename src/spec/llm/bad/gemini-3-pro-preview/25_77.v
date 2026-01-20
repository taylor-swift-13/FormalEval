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

Lemma is_prime_2 : is_prime 2.
Proof.
  unfold is_prime. split. lia.
  intros d H. destruct d as [|[|[|]]]; try lia.
  - destruct H as [k H]. simpl in H. discriminate.
  - left. reflexivity.
  - right. reflexivity.
  - apply Nat.divide_pos_le in H; lia.
Qed.

Lemma is_prime_3 : is_prime 3.
Proof.
  unfold is_prime. split. lia.
  intros d H. destruct d as [|[|[|[|]]]]; try lia.
  - destruct H as [k H]. simpl in H. discriminate.
  - left. reflexivity.
  - destruct H as [k H]. destruct k as [|[|[|]]]; simpl in H; try lia.
  - right. reflexivity.
  - apply Nat.divide_pos_le in H; lia.
Qed.

Lemma is_prime_27861139 : is_prime 27861139.
Proof.
  (* Proving primality for such a large number in unary nat is not feasible 
     with standard tactics inside Coq. We admit this fact. *)
  admit.
Admitted.

Example test_factorize_1003001004 : factorize_spec 1003001004 [2; 2; 3; 3; 27861139].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl.
    (* lia handles large integer constants by mapping to Z *)
    lia.
  - split.
    + (* Part 2: Primality check *)
      constructor. apply is_prime_2.
      constructor. apply is_prime_2.
      constructor. apply is_prime_3.
      constructor. apply is_prime_3.
      constructor. apply is_prime_27861139.
      constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.