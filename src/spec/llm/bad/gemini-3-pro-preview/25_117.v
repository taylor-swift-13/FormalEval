Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop := prime p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Definition check_prime (p : Z) : bool :=
  if prime_dec p then true else false.

Lemma check_prime_correct : forall p, check_prime p = true -> is_prime p.
Proof.
  intros p H. unfold check_prime in H.
  destruct (prime_dec p).
  - assumption.
  - discriminate.
Qed.

Example test_factorize_huge : factorize_spec 9999999968 [2; 2; 2; 2; 2; 7; 7; 6377551].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat (constructor; try (apply check_prime_correct; vm_compute; reflexivity)).
    + (* Part 3: Sorted check *)
      repeat (constructor; try lia).
Qed.