Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 999999%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (H1: 99 * 99 * 99 = 970299) by reflexivity.
    assert (H2: 100 * 100 * 100 = 1000000) by reflexivity.
    assert (Hpos: x * x * x = 999999) by exact Hx.
    assert (Habs: Z.abs x * Z.abs x * Z.abs x = Z.abs (x * x * x)).
    { rewrite Z.abs_mul. rewrite Z.abs_mul. reflexivity. }
    assert (Hcase: (x >= 0 \/ x < 0)) by lia.
    destruct Hcase as [Hge | Hlt].
    + assert (x >= 100 \/ x <= 99) by lia.
      destruct H as [Hge100 | Hle99].
      * assert (x * x * x >= 100 * 100 * 100) by nia.
        lia.
      * assert (x <= 99) by lia.
        assert (x >= 0) by lia.
        assert (x * x * x <= 99 * 99 * 99) by nia.
        lia.
    + assert (x <= -1) by lia.
      assert (x * x * x <= -1) by nia.
      lia.
Qed.