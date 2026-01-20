Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Ltac prove_pos_R :=
  apply Rlt_gt;
  match goal with
  | |- 0 < ?x / ?y => apply Rdiv_lt_0_compat; prove_pos_R
  | |- 0 < IZR ?n => apply IZR_lt; reflexivity
  end.

Ltac prove_neg_R :=
  match goal with
  | |- ?x < 0 =>
    match x with
    | - ?y => apply Ropp_0_lt_gt_contravar; prove_pos_R
    | IZR ?n => apply IZR_lt; reflexivity
    end
  end.

Example test_get_positive : get_positive_spec [0; -1.25; -1.5; -0.75; 9.9; -2.25; -1; -2; -3; -4; -5; 7; 0] [9.9; 7].
Proof.
  unfold get_positive_spec, filter, is_positive.
  repeat match goal with
  | |- context [Rgt_dec ?x 0] =>
    destruct (Rgt_dec x 0) as [Hgt | Hnotgt];
    [ 
      try (apply Rgt_irrefl in Hgt; contradiction);
      try (apply Rlt_not_gt in Hgt; [contradiction | prove_neg_R])
    | 
      try (exfalso; apply Hnotgt; prove_pos_R)
    ]
  end.
  reflexivity.
Qed.