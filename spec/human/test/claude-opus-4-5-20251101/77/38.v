Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 58%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (x <= 3 \/ x >= 4) as Hcase by lia.
    assert (x >= -3 \/ x <= -4) as Hcase2 by lia.
    destruct Hcase as [Hle3 | Hge4].
    + destruct Hcase2 as [Hgem3 | Hlem4].
      * assert (x = -3 \/ x = -2 \/ x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3) as Hvals by lia.
        destruct Hvals as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]];
        rewrite H1 in Hx || rewrite H2 in Hx || rewrite H3 in Hx || 
        rewrite H4 in Hx || rewrite H5 in Hx || rewrite H6 in Hx || rewrite H7 in Hx;
        simpl in Hx; lia.
      * assert (x * x * x <= -64) by nia.
        lia.
    + assert (x * x * x >= 64) by nia.
      lia.
Qed.