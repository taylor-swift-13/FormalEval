Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_1010 : is_prime_spec 1010 false.
Proof.
  unfold is_prime_spec.
  split.
  - intro H. lia.
  - intro H.
    split.
    + intro Hfalse. discriminate.
    + intro Hdiv.
      exfalso.
      assert (H2: 2 <= 2) by lia.
      assert (H3: 2 < 1010) by lia.
      specialize (Hdiv 2 H2 H3).
      compute in Hdiv.
      apply Hdiv.
      reflexivity.
Qed.