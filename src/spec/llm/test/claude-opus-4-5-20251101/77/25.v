Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_2 : iscube_spec (-999999)%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= -101 \/ n = -100 \/ n = -99 \/ n >= -98) as Hcases by lia.
    destruct Hcases as [Hle | [Heq | [Heq | Hge]]].
    + assert (n * n * n <= -101 * -101 * -101) by nia.
      simpl in H. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + assert (n <= -1 \/ n >= 0) as Hcases2 by lia.
      destruct Hcases2 as [Hneg | Hpos].
      * assert (n * n * n >= -98 * -98 * -98) by nia.
        simpl in H. lia.
      * assert (n * n * n >= 0) by nia. lia.
Qed.