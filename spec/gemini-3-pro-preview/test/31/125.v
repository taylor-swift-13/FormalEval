Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg_50 : is_prime_spec (-50) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-50) *)
    intros H.
    discriminate H.
  - (* Case: prime (-50) -> false = true *)
    intros Hprime.
    (* Definition of prime implies 1 < p *)
    destruct Hprime as [Hgt _].
    lia.
Qed.