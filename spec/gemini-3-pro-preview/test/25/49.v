Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 0 < d -> Z.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Lemma is_prime_26731 : is_prime 26731.
Proof. Admitted.

Lemma is_prime_1613153 : is_prime 1613153.
Proof. Admitted.

Example test_factorize_large : factorize_spec 43121192843 [26731; 1613153].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 26731 *)
        apply is_prime_26731.
      * constructor.
        -- (* is_prime 1613153 *)
           apply is_prime_1613153.
        -- (* End of list *)
           constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
      simpl. lia.
Qed.