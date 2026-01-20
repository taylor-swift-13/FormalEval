Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg_49 : is_prime_spec (-49) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime (-49) *)
    intros H.
    discriminate H.
  - (* Case: prime (-49) -> false = true *)
    intros Hprime.
    (* Definition of prime requires 1 < p *)
    destruct Hprime as [Hgt _].
    (* -49 is not greater than 1, contradiction *)
    lia.
Qed.