Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_17 : is_prime_spec 17 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    let p := eval vm_compute in (prime_dec 17) in
    match p with
    | left H => exact H
    | right _ => fail "17 is prime"
    end.
  - intros _. reflexivity.
Qed.