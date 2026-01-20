Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_2 : iscube_spec (-5)%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n >= 2) as Hcases by lia.
    destruct Hcases as [Hle | [Heq | [Heq | [Heq | Hge]]]].
    + assert (n * n * n <= -8) by nia. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + subst n. simpl in Hn. lia.
    + assert (n * n * n >= 8) by nia. lia.
Qed.