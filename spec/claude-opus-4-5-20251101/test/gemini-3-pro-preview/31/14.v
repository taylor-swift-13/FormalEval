Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_0 : is_prime_spec 0 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: n <= 1 *)
    intros H.
    reflexivity.
  - (* Case: n > 1 *)
    intros H.
    lia.
Qed.