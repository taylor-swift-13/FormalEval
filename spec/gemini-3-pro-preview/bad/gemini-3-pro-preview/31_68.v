Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_7937 : is_prime_spec 7937 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    let p := eval vm_compute in (prime_dec 7937) in
    match p with
    | left H => exact H
    | right _ => fail "Verification failed: 7937 should be prime"
    end.
  - intros _. reflexivity.
Qed.