Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 23 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    exfalso.
    destruct k as [|k'].
    + simpl in Hk. discriminate Hk.
    + destruct k' as [|k''].
      * simpl in Hk. discriminate Hk.
      * destruct k'' as [|k'''].
        -- simpl in Hk. discriminate Hk.
        -- assert (5 ^ Z.of_nat (S (S (S k'''))) >= 125).
           { destruct k''' as [|k''''].
             - simpl. lia.
             - assert (Z.of_nat (S (S (S (S k'''')))) >= 4) by lia.
               assert (5 ^ 4 = 625) by reflexivity.
               assert (5 ^ Z.of_nat (S (S (S (S k'''')))) >= 5 ^ 4).
               { apply Z.pow_le_mono_r; lia. }
               lia.
           }
           lia.
Qed.