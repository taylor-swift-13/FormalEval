Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg48 : is_prime_spec (-48) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-48) *)
    intros H.
    discriminate H.
  - (* Case: prime (-48) -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory implies 1 < p *)
    destruct Hprime as [Hgt1 _].
    (* Contradiction: 1 < -48 is false *)
    lia.
Qed.