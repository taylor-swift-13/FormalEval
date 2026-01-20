Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 26%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 2 \/ n >= 3) as Hcase by lia.
    assert (n >= -2 \/ n <= -3) as Hcase2 by lia.
    destruct Hcase as [Hle2 | Hge3].
    + destruct Hcase2 as [Hgem2 | Hlem3].
      * assert (n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2) as Hvals by lia.
        destruct Hvals as [Hn2 | [Hn1 | [Hn0 | [Hp1 | Hp2]]]];
          rewrite Hn2 in Hn || rewrite Hn1 in Hn || rewrite Hn0 in Hn || rewrite Hp1 in Hn || rewrite Hp2 in Hn;
          simpl in Hn; lia.
      * assert (n * n * n <= -27) by nia.
        lia.
    + assert (n * n * n >= 27) by nia.
      lia.
Qed.