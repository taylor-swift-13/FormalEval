Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 56%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 3 /\ n >= -3 \/ n > 3 \/ n < -3) as Hcases by lia.
    destruct Hcases as [[Hle Hge] | [Hgt | Hlt]].
    + assert (n = -3 \/ n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3) as Hn_cases by lia.
      destruct Hn_cases as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]];
      rewrite H1 in Hn || rewrite H2 in Hn || rewrite H3 in Hn || 
      rewrite H4 in Hn || rewrite H5 in Hn || rewrite H6 in Hn || rewrite H7 in Hn;
      simpl in Hn; lia.
    + assert (n * n * n >= 4 * 4 * 4) as Hmin.
      { assert (n >= 4) by lia.
        assert (n * n >= 16) by nia.
        nia. }
      lia.
    + assert (n * n * n <= (-4) * (-4) * (-4)) as Hmax.
      { assert (n <= -4) by lia.
        nia. }
      lia.
Qed.