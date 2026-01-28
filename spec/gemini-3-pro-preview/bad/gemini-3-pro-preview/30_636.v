Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rlt_dec 0 x then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Example test_get_positive : 
  get_positive_spec 
    [9.9; 25.221353337136023; 33.195768044846155; -2.25] 
    [9.9; 25.221353337136023; 33.195768044846155].
Proof.
  unfold get_positive_spec, is_positive.
  simpl.
  destruct (Rlt_dec 0 9.9) as [H1 | H1].
  2: { exfalso; apply H1; apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }
  destruct (Rlt_dec 0 25.221353337136023) as [H2 | H2].
  2: { exfalso; apply H2; apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }
  destruct (Rlt_dec 0 33.195768044846155) as [H3 | H3].
  2: { exfalso; apply H3; apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }
  destruct (Rlt_dec 0 (-2.25)) as [H4 | H4].
  - exfalso.
    apply Ropp_0_lt_gt_0 in H4.
    assert (Hpos: 0 < 2.25).
    { apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }
    apply (Rlt_asym _ _ Hpos H4).
  - reflexivity.
Qed.