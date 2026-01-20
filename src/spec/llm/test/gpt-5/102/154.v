Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example choose_num_spec_example : choose_num_spec 31%Z 31%Z (-1)%Z.
Proof.
  unfold choose_num_spec.
  right; right.
  split; [lia|].
  split.
  - intros Hex.
    destruct Hex as [z [Hz [Hxz Hyz]]].
    destruct Hz as [k Hzk].
    assert (z = 31%Z) by lia.
    subst z.
    lia.
  - reflexivity.
Qed.