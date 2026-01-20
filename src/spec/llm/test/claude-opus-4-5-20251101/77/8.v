Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 1729%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 11 \/ n = 12 \/ n >= 13) as Hcases by lia.
    destruct Hcases as [Hle11 | [Heq12 | Hge13]].
    + assert (n <= 11 -> n * n * n <= 1331) as Hbound.
      { intros. 
        assert (n <= 11) by assumption.
        assert (n * n <= 121) by nia.
        nia. }
      assert (n * n * n <= 1331) by (apply Hbound; assumption).
      lia.
    + subst n. simpl in Hn. lia.
    + assert (n >= 13 -> n * n * n >= 2197) as Hbound.
      { intros.
        assert (n >= 13) by assumption.
        assert (n * n >= 169) by nia.
        nia. }
      assert (n * n * n >= 2197) by (apply Hbound; assumption).
      lia.
Qed.