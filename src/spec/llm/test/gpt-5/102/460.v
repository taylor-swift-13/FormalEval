Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example choose_num_spec_example : choose_num_spec 1003%Z 1003%Z (-1%Z).
Proof.
  unfold choose_num_spec.
  right; right.
  split; [lia|].
  split.
  - intros [z [[k Hzk] [Hxz Hyz]]].
    subst z.
    destruct (Z_le_gt_dec k 501%Z) as [Hk_le|Hk_gt].
    + assert (2 * k <= 1002)%Z by lia.
      lia.
    + assert (502 <= k)%Z by lia.
      assert (1004 <= 2 * k)%Z by lia.
      lia.
  - lia.
Qed.