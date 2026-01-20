Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_39 : is_prime_spec 39 false.
Proof.
  unfold is_prime_spec.
  split.
  - intro H. lia.
  - intro H.
    split.
    + intro Hfalse. discriminate.
    + intro Hdiv.
      exfalso.
      assert (H2: 2 <= 3) by lia.
      assert (H3: 3 < 39) by lia.
      specialize (Hdiv 3 H2 H3).
      compute in Hdiv.
      apply Hdiv.
      reflexivity.
Qed.