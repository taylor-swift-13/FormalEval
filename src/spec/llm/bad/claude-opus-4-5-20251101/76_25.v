Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 21 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    exfalso.
    destruct k as [|k'].
    + simpl in Hk. lia.
    + destruct k' as [|k''].
      * simpl in Hk. lia.
      * destruct k'' as [|k'''].
        -- simpl in Hk. lia.
        -- destruct k''' as [|k''''].
           ++ simpl in Hk. lia.
           ++ destruct k'''' as [|k'''''].
              ** simpl in Hk. lia.
              ** assert (H5: Z.of_nat (S (S (S (S (S k'''''))))) >= 5) by lia.
                 assert (Hpow: 2 ^ 5 = 32) by reflexivity.
                 assert (Hge: 2 ^ Z.of_nat (S (S (S (S (S k'''''))))) >= 32).
                 {
                   replace 32 with (2 ^ 5) by reflexivity.
                   apply Z.pow_le_mono_r; lia.
                 }
                 lia.
Qed.