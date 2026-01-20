Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 82 1 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk1 Hk2]].
    rewrite Z.pow_1_l in Hk2.
    + lia.
    + apply Hk1.
Qed.