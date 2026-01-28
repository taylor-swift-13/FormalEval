Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg13 : is_prime_spec (-13) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-13) *)
    intros H.
    discriminate H.
  - (* Case: prime (-13) -> false = true *)
    intros Hprime.
    (* Definition of prime implies 1 < p *)
    destruct Hprime as [Hgt _].
    (* 1 < -13 is a contradiction *)
    lia.
Qed.