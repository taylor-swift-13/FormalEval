Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example choose_num_spec_example : choose_num_spec 6%Z 7%Z 6%Z.
Proof.
  unfold choose_num_spec.
  right; left.
  split; [lia|].
  split; [exists 3%Z; lia|].
  split; [lia|].
  split; [lia|].
  intros z Hz.
  destruct Hz as [[k Hzk] [Hxz Hyz]].
  rewrite Hzk in Hxz, Hyz.
  assert (Hk_low: 3%Z <= k) by lia.
  assert (Hk_high: k <= 3%Z) by lia.
  assert (Hk: k = 3%Z) by lia.
  rewrite Hk in Hzk.
  rewrite Hzk.
  lia.
Qed.