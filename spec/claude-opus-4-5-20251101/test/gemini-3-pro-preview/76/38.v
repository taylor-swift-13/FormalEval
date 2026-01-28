Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 36 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k Hk].
    destruct k.
    + simpl in Hk. discriminate.
    + rewrite Nat2Z.inj_succ in Hk.
      rewrite Z.pow_succ_r in Hk; [| apply Nat2Z.is_nonneg].
      apply (f_equal (fun z => z mod 5)) in Hk.
      rewrite Z.mul_comm in Hk.
      rewrite Z_mod_mult in Hk.
      simpl in Hk.
      discriminate.
Qed.