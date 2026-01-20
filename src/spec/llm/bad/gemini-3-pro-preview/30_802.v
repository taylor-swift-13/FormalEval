Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Lemma pos_real_def : forall n d, (0 < n)%Z -> (0 < d)%Z -> IZR n / IZR d > 0.
Proof.
  intros. apply Rlt_gt. apply Rdiv_lt_0_compat; apply IZR_lt; assumption.
Qed.

Ltac solve_pos :=
  match goal with
  | |- IZR _ / IZR _ > 0 => apply pos_real_def; vm_compute; reflexivity
  | |- IZR _ > 0 => apply Rlt_gt; apply IZR_lt; vm_compute; reflexivity
  | |- ?x > 0 => 
      try (apply pos_real_def; vm_compute; reflexivity)
  end.

Ltac solve_neg_contra :=
  match goal with
  | H: 0 > 0 |- False => apply Rlt_irrefl in H; assumption
  | H: IZR _ > 0 |- False => 
      apply Rgt_lt in H; apply IZR_lt in H; vm_compute in H; contradiction
  | H: Ropp ?x > 0 |- False =>
      assert (Hx : x > 0); [ solve_pos |
        apply Rgt_lt in H; apply Rgt_lt in Hx;
        apply Ropp_lt_gt_0_contravar in Hx;
        apply Rlt_asym with (r1 := -x) (r2 := 0); assumption
      ]
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0.5; 0; -4; 2.5; 5; -2.2; -8; 7.7; 9.9; -10.5; -10.338878645170468; -8] [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (
    match goal with
    | |- context [Rgt_dec ?x 0] =>
      destruct (Rgt_dec x 0); 
      [ try (exfalso; solve_neg_contra)
      | try (exfalso; apply n; solve_pos)
      ]
    end
  ).
  reflexivity.
Qed.