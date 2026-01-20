Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 11 23 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    destruct k.
    + simpl in Hk2. discriminate.
    + assert (23 ^ 1 <= 23 ^ Z.pos p).
      { apply Z.pow_le_mono_r; lia. }
      change (23 ^ 1) with 23 in H.
      lia.
    + lia.
Qed.