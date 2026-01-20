Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [0.5%R; (-1)%R; 24.93175152910768%R; (-4)%R; 2.5%R; 5%R; (-2.651030586877352)%R; (-8)%R; 7.7%R; 9.9%R; (-10.5)%R; (-8)%R; 9.9%R]
    [0.5%R; 24.93175152910768%R; 2.5%R; 5%R; 7.7%R; 9.9%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  replace (if Rlt_dec 0 0.5%R then true else false) with true by (destruct (Rlt_dec 0 0.5%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 (-1)%R then true else false) with false by (destruct (Rlt_dec 0 (-1)%R); [lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 24.93175152910768%R then true else false) with true by (destruct (Rlt_dec 0 24.93175152910768%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 (-4)%R then true else false) with false by (destruct (Rlt_dec 0 (-4)%R); [lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 2.5%R then true else false) with true by (destruct (Rlt_dec 0 2.5%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 5%R then true else false) with true by (destruct (Rlt_dec 0 5%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 (-2.651030586877352)%R then true else false) with false by (destruct (Rlt_dec 0 (-2.651030586877352)%R); [lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 (-8)%R then true else false) with false by (destruct (Rlt_dec 0 (-8)%R); [lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 7.7%R then true else false) with true by (destruct (Rlt_dec 0 7.7%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 9.9%R then true else false) with true by (destruct (Rlt_dec 0 9.9%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 (-10.5)%R then true else false) with false by (destruct (Rlt_dec 0 (-10.5)%R); [lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 (-8)%R then true else false) with false by (destruct (Rlt_dec 0 (-8)%R); [lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 9.9%R then true else false) with true by (destruct (Rlt_dec 0 9.9%R); [reflexivity | exfalso; lra]).
  simpl.
  reflexivity.
Qed.