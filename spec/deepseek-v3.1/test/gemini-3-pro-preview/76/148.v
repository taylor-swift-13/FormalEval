Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 3 65536 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    destruct k.
    + simpl in Hk_eq.
      discriminate.
    + assert (65536 <= 65536 ^ Z.pos p).
      {
        rewrite <- (Z.pow_1_r 65536) at 1.
        apply Z.pow_le_mono_r; lia.
      }
      lia.
    + lia.
Qed.