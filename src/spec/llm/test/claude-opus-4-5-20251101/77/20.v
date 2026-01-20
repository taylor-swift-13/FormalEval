Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 57%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 3 \/ n >= 4) as Hcases by lia.
    assert (n >= -3 \/ n <= -4) as Hcases2 by lia.
    destruct Hcases as [Hle3 | Hge4].
    + destruct Hcases2 as [Hgem3 | Hlem4].
      * assert (n = -3 \/ n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3) as Hvals by lia.
        destruct Hvals as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]];
        rewrite H1 in Hn || rewrite H2 in Hn || rewrite H3 in Hn || 
        rewrite H4 in Hn || rewrite H5 in Hn || rewrite H6 in Hn || rewrite H7 in Hn;
        simpl in Hn; lia.
      * assert (n * n * n <= -64) by lia.
        lia.
    + assert (n * n * n >= 64) by lia.
      lia.
Qed.