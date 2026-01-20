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

Lemma check_product : fold_right mult 1 [239; 180423401] = 43121192839.
Proof. Admitted.

Lemma check_prime_239 : is_prime 239.
Proof. Admitted.

Lemma check_prime_180423401 : is_prime 180423401.
Proof. Admitted.

Lemma check_sorted : Sorted le [239; 180423401].
Proof. Admitted.

Example test_factorize_43121192839 : factorize_spec 43121192839 [239; 180423401].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    apply check_product.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * apply check_prime_239.
      * constructor.
        -- apply check_prime_180423401.
        -- constructor.
    + (* Part 3: Sorted check *)
      apply check_sorted.
Qed.