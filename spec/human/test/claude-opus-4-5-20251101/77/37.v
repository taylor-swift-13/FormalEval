Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec (-62)%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (x <= -4 \/ x = -3 \/ x = -2 \/ x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x >= 4) as Hcases by lia.
    destruct Hcases as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
    + assert (x * x * x <= -64) by nia.
      lia.
    + subst x. simpl in Hx. lia.
    + subst x. simpl in Hx. lia.
    + subst x. simpl in Hx. lia.
    + subst x. simpl in Hx. lia.
    + subst x. simpl in Hx. lia.
    + subst x. simpl in Hx. lia.
    + subst x. simpl in Hx. lia.
    + assert (x * x * x >= 64) by nia.
      lia.
Qed.