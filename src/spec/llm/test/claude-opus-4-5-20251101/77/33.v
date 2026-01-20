Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 119%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 4 /\ n >= -4 \/ n > 4 \/ n < -4) as Hcases by lia.
    destruct Hcases as [[Hle Hge] | [Hgt | Hlt]].
    + assert (n = -4 \/ n = -3 \/ n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4) as Hvals by lia.
      destruct Hvals as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]];
      rewrite H in Hn; simpl in Hn; lia.
    + assert (n >= 5) as H5 by lia.
      assert (n * n * n >= 5 * 5 * 5) as Hcube.
      { assert (n * n >= 25) by nia. nia. }
      lia.
    + assert (n <= -5) as H5 by lia.
      assert (n * n * n <= -125) as Hcube.
      { assert (n * n >= 25) by nia.
        assert (n * n * n <= -5 * 25) by nia.
        lia. }
      lia.
Qed.