Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Definition check_prime (n : Z) : bool :=
  if prime_dec n then true else false.

Lemma check_prime_correct : forall n, check_prime n = true -> prime n.
Proof.
  intros n H.
  unfold check_prime in H.
  destruct (prime_dec n).
  - assumption.
  - discriminate H.
Qed.

Example test_is_prime_34981 : is_prime_spec 34981 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    apply check_prime_correct.
    vm_compute.
    reflexivity.
  - intros _.
    reflexivity.
Qed.