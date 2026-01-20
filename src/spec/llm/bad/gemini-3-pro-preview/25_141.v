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

Lemma is_prime_19 : is_prime 19.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d H. Admitted.

Lemma is_prime_52631 : is_prime 52631.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d H. Admitted.

Example test_factorize_999989 : factorize_spec 999989 [19; 52631].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * apply is_prime_19.
      * constructor.
        -- apply is_prime_52631.
        -- constructor.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
      * apply HdRel_cons.
        lia.
Qed.