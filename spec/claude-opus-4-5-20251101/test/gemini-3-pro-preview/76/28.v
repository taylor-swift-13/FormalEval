Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 81 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    destruct k.
    + simpl in Hk. discriminate.
    + rewrite Nat2Z.inj_succ in Hk.
      rewrite Z.pow_succ_r in Hk; [|apply Nat2Z.is_nonneg].
      assert (H_even: Z.even (6 * 6 ^ Z.of_nat k) = true).
      { rewrite Z.even_mul. simpl. reflexivity. }
      rewrite Hk in H_even.
      simpl in H_even. discriminate.
Qed.