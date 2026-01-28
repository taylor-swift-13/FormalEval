Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_13441 : is_prime_spec 13441 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    (* Use the decidability of primality in Z *)
    assert (Hcheck: (if prime_dec 13441 then true else false) = true).
    { vm_compute. reflexivity. }
    destruct (prime_dec 13441) as [Hprime | Hnot].
    + exact Hprime.
    + discriminate Hcheck.
  - intros _. reflexivity.
Qed.