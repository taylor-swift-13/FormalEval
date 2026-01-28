Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_37 : is_prime_spec 37 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    (* We use the decidability of primality from Znumtheory to prove prime 37. *)
    (* prime_dec 37 returns {prime 37} + {~ prime 37} *)
    pose proof (prime_dec 37) as Hdec.
    (* We force computation of the decision procedure to get the left branch *)
    vm_compute in Hdec.
    destruct Hdec as [Hprime | Hnotprime].
    + (* Case: prime 37 *)
      exact Hprime.
    + (* Case: ~ prime 37. This branch is unreachable for 37. *)
      (* If vm_compute works correctly, this branch is not generated. *)
      (* If it is generated, we fail because 37 should be prime. *)
      fail "prime_dec 37 computed to right (not prime)".
  - (* Case: prime 37 -> true = true *)
    intros _.
    reflexivity.
Qed.