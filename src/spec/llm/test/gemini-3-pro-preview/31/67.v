Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg17 : is_prime_spec (-17) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-17) *)
    intros H.
    discriminate H.
  - (* Case: prime (-17) -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory requires 1 < p *)
    destruct Hprime as [Hgt _].
    (* 1 < -17 is a contradiction *)
    lia.
Qed.