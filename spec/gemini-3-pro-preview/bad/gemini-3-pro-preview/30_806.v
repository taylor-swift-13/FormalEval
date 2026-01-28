Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [0.5; 2.5; 5; -2.2; -2.651030586877352; -8; 7.7; 9.9; -10.5; 9.9] 
  [0.5; 2.5; 5; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  cbv [filter].
  Ltac solve_pos := 
    apply Rlt_gt; 
    try (apply IZR_lt; reflexivity); 
    try (apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity).
  Ltac solve_neg := 
    match goal with
    | |- IZR _ <= 0 => apply IZR_le; reflexivity
    | |- - _ <= 0 => 
         rewrite <- Ropp_0; apply Ropp_le_cancel; apply Rlt_le; solve_pos
    end.
  repeat match goal with
  | |- context [Rgt_dec ?x 0] =>
      destruct (Rgt_dec x 0);
      [ 
        try (exfalso; match goal with H: x > 0 |- _ => apply Rlt_not_le in H; apply H end; solve_neg)
      | 
        try (exfalso; match goal with H: ~ x > 0 |- _ => apply H end; solve_pos)
      ]
  end.
  reflexivity.
Qed.