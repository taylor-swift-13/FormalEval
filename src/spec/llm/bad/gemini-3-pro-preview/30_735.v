Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Ltac prove_pos_lit :=
  try apply Rlt_gt;
  repeat (apply Rdiv_lt_0_compat || apply Rmult_lt_0_compat || apply Rplus_lt_0_compat || apply Rinv_0_lt_compat);
  try (apply IZR_lt; reflexivity).

Example test_get_positive : get_positive_spec 
  [-2.651030586877352; -4; 2.5; 5; -2.651030586877352; -8; 8.193677988449515; 7.7; 9.9; -10.5; 9.9; -2.2] 
  [2.5; 5; 8.193677988449515; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | [ |- context [Rgt_dec ?x 0] ] =>
    destruct (Rgt_dec x 0);
    [ try (exfalso; apply Rlt_not_le in r; apply r; 
           try (apply IZR_le; reflexivity);
           try (apply Rlt_le; match x with | -?c => apply Ropp_lt_gt_0_contravar; prove_pos_lit end)
          )
    | try (exfalso; apply n; prove_pos_lit) ]
  end.
  reflexivity.
Qed.