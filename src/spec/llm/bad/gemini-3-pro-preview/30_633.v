Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_bool (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgt_bool x 0) l.

Example test_get_positive : get_positive_spec [-89.04346588476734; 32.97170491287429; -2.25] [32.97170491287429].
Proof.
  unfold get_positive_spec, Rgt_bool.
  simpl.
  destruct (Rgt_dec (-89.04346588476734) 0) as [H1|H1].
  - exfalso.
    assert (C: -89.04346588476734 < 0).
    { apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }
    apply Rlt_asym in C. apply C in H1. assumption.
  - destruct (Rgt_dec 32.97170491287429 0) as [H2|H2].
    + destruct (Rgt_dec (-2.25) 0) as [H3|H3].
      * exfalso.
        assert (C: -2.25 < 0).
        { apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }
        apply Rlt_asym in C. apply C in H3. assumption.
      * reflexivity.
    + exfalso. apply H2.
      apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity.
Qed.