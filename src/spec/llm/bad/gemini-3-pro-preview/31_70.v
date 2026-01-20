Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_42043 : is_prime_spec 42043 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    (* Use computational reflection with prime_dec from Znumtheory *)
    let p := eval vm_compute in (prime_dec 42043) in
    match p with
    | left H => exact H
    | right _ => fail "42043 is prime, but prime_dec returned false"
    end.
  - intros _. reflexivity.
Qed.