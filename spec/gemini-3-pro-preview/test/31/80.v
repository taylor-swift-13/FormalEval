Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg16 : is_prime_spec (-16) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-16) *)
    intros H.
    discriminate H.
  - (* Case: prime (-16) -> false = true *)
    intros Hprime.
    (* By definition of prime, we must have 1 < n *)
    destruct Hprime as [Hgt _].
    (* 1 < -16 is a contradiction *)
    lia.
Qed.