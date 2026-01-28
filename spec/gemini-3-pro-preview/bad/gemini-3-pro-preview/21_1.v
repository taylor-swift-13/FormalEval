Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope R_scope.

Definition rescale_to_unit_spec (numbers : list R) (result : list R) : Prop :=
  exists (mi ma : R),
    (In mi numbers /\ forall x, In x numbers -> mi <= x) /\
    (In ma numbers /\ forall x, In x numbers -> x <= ma) /\
    ma <> mi /\
    result = map (fun x => (x - mi) * (1 / (ma - mi))) numbers.

(* Helper lemma to prove 2.0 < 49.9 using basic Real arithmetic, avoiding Lra and Field tactics *)
Lemma two_lt_49_9 : 2.0 < 49.9.
Proof.
  (* Multiply both sides by 10 to clear the decimal/division *)
  apply Rmult_lt_reg_r with (r := 10).
  - apply IZR_lt. reflexivity.
  - (* 49.9 is parsed as 499 / 10 *)
    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    + rewrite Rmult_1_r.
      (* Now compare 2.0 * 10 and 499 *)
      (* 2.0 * 10 = IZR 2 * IZR 10 = IZR 20 *)
      rewrite <- mult_IZR.
      apply IZR_lt. reflexivity.
    + apply IZR_neq. discriminate.
Qed.

Example test_rescale : rescale_to_unit_spec [2.0; 49.9] [0.0; 1.0].
Proof.
  unfold rescale_to_unit_spec.
  exists 2.0, 49.9.
  repeat split.
  
  (* 1. Prove 2.0 is in the list *)
  - simpl. left. reflexivity.
  
  (* 2. Prove 2.0 is the minimum *)
  - intros x H. simpl in H. destruct H as [H | [H | H]]; try contradiction.
    + rewrite <- H. right. reflexivity.
    + rewrite <- H. apply Rlt_le. apply two_lt_49_9.
    
  (* 3. Prove 49.9 is in the list *)
  - simpl. right. left. reflexivity.
  
  (* 4. Prove 49.9 is the maximum *)
  - intros x H. simpl in H. destruct H as [H | [H | H]]; try contradiction.
    + rewrite <- H. apply Rlt_le. apply two_lt_49_9.
    + rewrite <- H. right. reflexivity.
    
  (* 5. Prove ma <> mi *)
  - apply Rgt_not_eq. apply two_lt_49_9.
  
  (* 6. Prove result matches calculation *)
  - simpl. f_equal.
    + (* First element: (2.0 - 2.0) * ... = 0 *)
      rewrite Rminus_diag.
      rewrite Rmult_0_l.
      reflexivity.
    + f_equal.
      * (* Second element: (49.9 - 2.0) * (1 / (49.9 - 2.0)) = 1 *)
        (* This is of the form x * (1/x) = 1 *)
        rewrite Rinv_r.
        -- reflexivity.
        -- (* Prove x <> 0, i.e., 49.9 - 2.0 <> 0 *)
           apply Rgt_not_eq.
           apply Rgt_minus.
           apply two_lt_49_9.
      * reflexivity.
Qed.