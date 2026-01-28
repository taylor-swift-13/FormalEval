Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_7933 : is_prime_spec 7933 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    assert (H_dec: if prime_dec 7933 then True else False).
    { vm_compute. exact I. }
    destruct (prime_dec 7933) as [Hp | Hnp] eqn:E.
    + exact Hp.
    + rewrite E in H_dec. contradiction.
  - intros _. reflexivity.
Qed.