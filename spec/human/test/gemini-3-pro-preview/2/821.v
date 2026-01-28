Require Import Reals.
Require Import Psatz.
Require Import ZArith.
Open Scope R_scope.

Definition floor (x : R) : Z := (up x) - 1.

Lemma floor_unique : forall (x : R) (z : Z), IZR z <= x < IZR z + 1 -> floor x = z.
Proof.
  intros x z [Hlow Hhigh].
  unfold floor.
  destruct (archimed x) as [Hup_gt Hup_le].
  assert (H_up_val : up x = (z + 1)%Z).
  {
    assert (z < up x)%Z.
    { apply lt_IZR. eapply Rle_lt_trans; eauto. }
    assert (up x < z + 2)%Z.
    { 
      apply lt_IZR. 
      rewrite plus_IZR. 
      simpl.
      lra.
    }
    lia.
  }
  rewrite H_up_val.
  lia.
Qed.

Definition problem_2_pre(x : R) : Prop :=
  x > 0.

Definition problem_2_spec (x frac : R) : Prop :=
  frac = x - IZR (floor x) /\
  0 <= frac < 1.

Example test_case : problem_2_spec 3.0238454764740426 0.0238454764740426.
Proof.
  unfold problem_2_spec.
  split.
  - assert (H_floor : floor 3.0238454764740426 = 3%Z).
    {
      apply floor_unique.
      split.
      + simpl. lra.
      + simpl. lra.
    }
    rewrite H_floor.
    simpl.
    lra.
  - lra.
Qed.