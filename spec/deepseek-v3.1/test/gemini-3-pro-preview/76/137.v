Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 81 16777217 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    destruct k.
    + simpl in Hk2. discriminate Hk2.
    + assert (H: 16777217 ^ 1 <= 16777217 ^ Z.pos p).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in H.
      simpl in H.
      lia.
    + lia.
Qed.