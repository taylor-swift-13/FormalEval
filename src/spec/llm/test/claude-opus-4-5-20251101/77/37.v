Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec (-62%Z) false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= -4 \/ n = -3 \/ n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n >= 4) as Hcases by lia.
    destruct Hcases as [H4 | [H3 | [H2 | [H1 | [H0 | [Hp1 | [Hp2 | [Hp3 | Hp4]]]]]]]].
    + assert (n * n * n <= -64) by lia. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + assert (n * n * n >= 64) by lia. lia.
Qed.