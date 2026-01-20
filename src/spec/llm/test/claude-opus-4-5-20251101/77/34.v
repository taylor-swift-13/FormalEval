Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec (-28)%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= -4 \/ n = -3 \/ n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n >= 4) as Hcases by lia.
    destruct Hcases as [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]].
    + assert (n * n * n <= -64) by lia. lia.
    + rewrite H1 in Hn. simpl in Hn. lia.
    + rewrite H1 in Hn. simpl in Hn. lia.
    + rewrite H1 in Hn. simpl in Hn. lia.
    + rewrite H1 in Hn. simpl in Hn. lia.
    + rewrite H1 in Hn. simpl in Hn. lia.
    + rewrite H1 in Hn. simpl in Hn. lia.
    + rewrite H1 in Hn. simpl in Hn. lia.
    + assert (n * n * n >= 64) by lia. lia.
Qed.