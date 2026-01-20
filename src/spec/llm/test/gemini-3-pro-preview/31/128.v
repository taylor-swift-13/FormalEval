Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_neg28 : is_prime_spec (-28) false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    (* prime p implies 1 < p *)
    destruct Hprime as [Hgt _].
    (* 1 < -28 is a contradiction *)
    lia.
Qed.