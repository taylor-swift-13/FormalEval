Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 730%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 8 \/ n >= 10 \/ n = 9) as Hcases by lia.
    destruct Hcases as [Hle8 | [Hge10 | Heq9]].
    + assert (n <= -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) as Hsmall by lia.
      destruct Hsmall as [Hneg | [H0 | [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | H8]]]]]]]]].
      * assert (n * n * n <= -1) by lia. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
      * subst n. simpl in Hn. lia.
    + assert (n * n * n >= 1000) by lia. lia.
    + subst n. simpl in Hn. lia.
Qed.