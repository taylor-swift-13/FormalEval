Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_2 : iscube_spec 58%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 3 \/ n >= 4) as Hcase by lia.
    destruct Hcase as [Hle3 | Hge4].
    + assert (n <= -4 \/ n = -3 \/ n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3) as Hcases by lia.
      destruct Hcases as [Hlem4 | [Heqm3 | [Heqm2 | [Heqm1 | [Heq0 | [Heq1 | [Heq2 | Heq3]]]]]]].
      * assert (n * n * n <= -64) by nia. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
    + assert (n * n * n >= 64) by nia. lia.
Qed.