Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_67 : is_prime_spec 67 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    (* Use computational reflection to prove prime 67 *)
    let p := eval vm_compute in (prime_dec 67) in
    match p with
    | left H => exact H
    | right _ => fail "67 is prime"
    end.
  - intros _.
    reflexivity.
Qed.