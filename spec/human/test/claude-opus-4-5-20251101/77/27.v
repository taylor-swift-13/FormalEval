Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 123%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (H4: x <= 4) by lia.
    assert (H5: x >= 5 -> x * x * x >= 125) by (intros; nia).
    assert (Hn5: x <= -5 -> x * x * x <= -125) by (intros; nia).
    assert (Hrange: -4 <= x <= 4) by lia.
    destruct (Z.eq_dec x 0); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x 1); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x (-1)); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x 2); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x (-2)); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x 3); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x (-3)); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x 4); [subst; simpl in Hx; lia|].
    destruct (Z.eq_dec x (-4)); [subst; simpl in Hx; lia|].
    lia.
Qed.