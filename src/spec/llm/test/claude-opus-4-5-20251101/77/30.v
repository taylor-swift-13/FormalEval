Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_2 : iscube_spec (-1000001)%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= -101 \/ n = -100 \/ (-99 <= n <= 99) \/ n = 100 \/ n >= 101) as Hcases by lia.
    destruct Hcases as [Hle | [Heq | [Hmid | [Heq2 | Hge]]]].
    + assert (n * n * n <= -101 * -101 * -101) by nia.
      simpl in H. lia.
    + rewrite Heq in Hn. simpl in Hn. lia.
    + assert (n * n * n >= -99 * 99 * 99) by nia.
      assert (n * n * n <= 99 * 99 * 99) by nia.
      lia.
    + rewrite Heq2 in Hn. simpl in Hn. lia.
    + assert (n * n * n >= 101 * 101 * 101) by nia.
      lia.
Qed.