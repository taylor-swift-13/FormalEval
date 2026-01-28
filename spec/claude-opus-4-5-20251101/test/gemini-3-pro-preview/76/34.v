Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 82 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k Hk].
    destruct k. { simpl in Hk. discriminate. }
    destruct k. { simpl in Hk. discriminate. }
    destruct k. { simpl in Hk. discriminate. }
    destruct k. { simpl in Hk. discriminate. }
    destruct k. { simpl in Hk. discriminate. }
    replace (Z.of_nat (S (S (S (S (S k)))))) with (5 + Z.of_nat k) in Hk by lia.
    rewrite Z.pow_add_r in Hk; [| lia | lia].
    change (3 ^ 5) with 243 in Hk.
    assert (0 < 3 ^ Z.of_nat k).
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.