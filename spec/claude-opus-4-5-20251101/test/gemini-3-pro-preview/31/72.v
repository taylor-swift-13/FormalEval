Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_10000000029 : is_prime_spec 10000000029 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    lia.
  - intros _.
    split.
    + intros H.
      discriminate H.
    + intros H.
      specialize (H 3).
      assert (H_bounds: 2 <= 3 /\ 3 < 10000000029) by lia.
      destruct H_bounds as [H_le H_lt].
      specialize (H H_le H_lt).
      assert (H_rem: Z.rem 10000000029 3 = 0) by reflexivity.
      rewrite H_rem in H.
      contradiction.
Qed.