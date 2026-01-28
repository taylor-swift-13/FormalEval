Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg_20 : is_prime_spec (-20) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-20) *)
    intros H.
    discriminate H.
  - (* Case: prime (-20) -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory requires 1 < p *)
    destruct Hprime as [Hgt1 _].
    (* -20 is not greater than 1 *)
    lia.
Qed.