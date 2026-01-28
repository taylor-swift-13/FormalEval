Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_31 : is_prime_spec 31 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    assert (H : prime 31).
    {
      let val := eval vm_compute in (prime_dec 31) in
      match val with
      | left p => exact p
      | right _ => fail "31 is prime"
      end.
    }
    exact H.
  - intros _.
    reflexivity.
Qed.