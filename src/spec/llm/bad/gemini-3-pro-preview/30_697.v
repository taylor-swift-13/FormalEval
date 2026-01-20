Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_skip : forall x l l', x <= 0 -> get_positive_rel l l' -> get_positive_rel (x::l) l'
| gp_keep : forall x l l', x > 0 -> get_positive_rel l l' -> get_positive_rel (x::l) (x::l').

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Ltac solve_pos :=
  try (apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity).

Ltac solve_neg :=
  try (apply Rlt_le; apply Ropp_lt_gt_0_contravar; solve_pos).

Example test_get_positive : get_positive_spec 
  [7.878953248636265; 25.12472520208241; 33.195768044846155; -2.25; 33.195768044846155] 
  [7.878953248636265; 25.12472520208241; 33.195768044846155; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  apply gp_keep; [ solve_pos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_skip; [ solve_neg | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_nil.
Qed.