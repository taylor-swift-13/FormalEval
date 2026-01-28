Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example test_choose_num : choose_num_spec 34 101 100.
Proof.
  unfold choose_num_spec.
  right. left.
  repeat split.
  - lia.
  - exists 50. lia.
  - lia.
  - lia.
  - intros z H.
    destruct H as [(k & Heq) (Hge & Hle)].
    assert (z <> 101).
    {
      intro H101.
      rewrite H101 in Heq.
      lia.
    }
    lia.
Qed.