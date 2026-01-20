Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example choose_num_spec_example : choose_num_spec 10%Z 12%Z 12%Z.
Proof.
  unfold choose_num_spec.
  right; left.
  split; [lia|].
  split; [exists 6%Z; lia|].
  split; [lia|].
  split; [lia|].
  intros z Hz.
  destruct Hz as [[k Hzk] [Hxz Hyz]].
  lia.
Qed.