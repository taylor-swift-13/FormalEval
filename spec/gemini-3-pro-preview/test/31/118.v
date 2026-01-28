Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg39 : is_prime_spec (-39) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-39) *)
    intros H.
    discriminate H.
  - (* Case: prime (-39) -> false = true *)
    intros Hprime.
    (* Definition of prime implies 1 < p *)
    destruct Hprime as [Hgt1 _].
    (* -39 is not greater than 1, contradiction *)
    lia.
Qed.