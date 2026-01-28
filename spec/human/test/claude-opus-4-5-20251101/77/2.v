Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 2%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (x <= 0 \/ x = 1 \/ x >= 2) as Hcases by lia.
    destruct Hcases as [Hneg | [Hone | Hpos]].
    + assert (x * x * x <= 0) by nia.
      lia.
    + subst x.
      simpl in Hx.
      lia.
    + assert (x * x * x >= 8) by nia.
      lia.
Qed.