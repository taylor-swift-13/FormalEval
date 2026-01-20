Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_1009 : is_prime_spec 1009 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    match goal with
    | [ |- prime 1009 ] =>
        let val := eval vm_compute in (prime_dec 1009) in
        match val with
        | left H => exact H
        | right _ => fail "1009 is not prime"
        end
    end.
  - intros _.
    reflexivity.
Qed.