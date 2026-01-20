Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_101 : is_prime_spec 101 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    (* We use the decidability of primality to construct the proof witness *)
    pose proof (prime_dec 101) as H.
    (* Compute the decision to reduce it to 'left Hprime' *)
    vm_compute in H.
    destruct H as [Hprime | Hnot].
    + exact Hprime.
  - intros _.
    reflexivity.
Qed.