Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_23 : is_prime_spec 23 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    pose (check := if prime_dec 23 then true else false).
    assert (Hcheck : check = true) by (vm_compute; reflexivity).
    unfold check in Hcheck.
    destruct (prime_dec 23) as [Hprime | Hnot].
    + exact Hprime.
    + discriminate Hcheck.
  - intros _. reflexivity.
Qed.