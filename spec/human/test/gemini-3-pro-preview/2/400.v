Require Import Reals.
Require Import Psatz.
Require Import ZArith.
Open Scope R_scope.

(* Since Coquelicot is not available, we define floor using the standard library's 'up' function.
   'up' gives the ceiling for non-integers (specifically, up x is the unique integer such that x < up x <= x + 1).
   We define floor x = up x - 1. *)
Definition floor (x : R) : Z := (up x) - 1.

(* Lemma to prove the value of floor given bounds *)
Lemma floor_unique : forall (x : R) (z : Z), IZR z <= x < IZR z + 1 -> floor x = z.
Proof.
  intros x z [Hlow Hhigh].
  unfold floor.
  (* archimed x gives: IZR (up x) > x /\ IZR (up x) - x <= 1 *)
  destruct (archimed x) as [Hup_gt Hup_le].
  
  (* We need to show (up x - 1) = z, which is equivalent to up x = z + 1 *)
  assert (H_up_val : up x = (z + 1)%Z).
  {
    (* Show z < up x *)
    assert (z < up x)%Z.
    { apply lt_IZR. eapply Rle_lt_trans; eauto. }
    
    (* Show up x < z + 2 *)
    assert (up x < z + 2)%Z.
    { 
      apply lt_IZR. 
      rewrite plus_IZR. 
      simpl.
      (* From Hup_le: IZR (up x) <= x + 1 *)
      (* From Hhigh: x < IZR z + 1 *)
      lra.
    }
    
    (* Since z < up x < z + 2, up x must be z + 1 *)
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

Example test_case : problem_2_spec 102623306.32845166325569153 0.32845166325569153.
Proof.
  unfold problem_2_spec.
  split.
  - (* Prove 0.32845166325569153 = 102623306.32845166325569153 - floor(...) *)
    assert (H_floor : floor 102623306.32845166325569153 = 102623306%Z).
    {
      apply floor_unique.
      split.
      + simpl. lra.
      + simpl. lra.
    }
    rewrite H_floor.
    simpl.
    lra.
  - (* Prove 0 <= 0.32845166325569153 < 1 *)
    lra.
Qed.