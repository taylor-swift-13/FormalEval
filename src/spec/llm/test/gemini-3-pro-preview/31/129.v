Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg_101 : is_prime_spec (-101) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-101) *)
    intros H.
    discriminate H.
  - (* Case: prime (-101) -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory includes 1 < p *)
    destruct Hprime as [Hgt _].
    (* Contradiction: 1 < -101 is false *)
    lia.
Qed.