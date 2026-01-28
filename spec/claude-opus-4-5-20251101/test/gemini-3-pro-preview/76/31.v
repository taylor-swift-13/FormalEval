Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 2 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k Hk].
    destruct k.
    + simpl in Hk.
      discriminate Hk.
    + destruct k.
      * simpl in Hk.
        discriminate Hk.
      * assert (H: 5 ^ 2 <= 5 ^ Z.of_nat (S (S k))).
        { apply Z.pow_le_mono_r; lia. }
        rewrite Hk in H.
        simpl in H.
        lia.
Qed.