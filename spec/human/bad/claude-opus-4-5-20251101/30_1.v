Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope R_scope.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition is_positive (r : R) : Prop :=
  r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

(* Define the input and output lists *)
Definition input_list : list R := 
  [IZR (-1); IZR (-2); IZR 4; IZR 5; IZR 6].

Definition output_list : list R := 
  [IZR 4; IZR 5; IZR 6].

(* Helper lemmas for IZR positivity *)
Lemma IZR_4_pos : IZR 4 > 0.
Proof.
  unfold IZR. simpl.
  rewrite <- (Rplus_0_l 0).
  apply Rplus_lt_compat.
  - rewrite <- (Rplus_0_l 0).
    apply Rplus_lt_compat; apply Rlt_0_1.
  - rewrite <- (Rplus_0_l 0).
    apply Rplus_lt_compat; apply Rlt_0_1.
Qed.

Lemma IZR_5_pos : IZR 5 > 0.
Proof.
  unfold IZR. simpl.
  apply Rlt_gt.
  apply Rplus_lt_0_compat.
  - apply Rlt_gt. apply IZR_4_pos.
  - apply Rlt_0_1.
Qed.

Lemma IZR_6_pos : IZR 6 > 0.
Proof.
  unfold IZR. simpl.
  apply Rlt_gt.
  apply Rplus_lt_0_compat.
  - apply Rlt_gt. apply IZR_5_pos.
  - apply Rlt_0_1.
Qed.

Lemma IZR_neg1_not_pos : ~ (IZR (-1) > 0).
Proof.
  unfold IZR. simpl.
  intro H.
  apply Rgt_lt in H.
  assert (H1: -1 < 0) by (apply Ropp_lt_gt_0_contravar; apply Rlt_0_1).
  apply (Rlt_irrefl 0).
  apply Rlt_trans with (-1); assumption.
Qed.

Lemma IZR_neg2_not_pos : ~ (IZR (-2) > 0).
Proof.
  unfold IZR. simpl.
  intro H.
  apply Rgt_lt in H.
  assert (H1: -(1+1) < 0).
  { apply Ropp_lt_gt_0_contravar.
    apply Rplus_lt_0_compat; apply Rlt_0_1. }
  apply (Rlt_irrefl 0).
  apply Rlt_trans with (-(1+1)); assumption.
Qed.

Example problem_30_test : problem_30_spec input_list output_list.
Proof.
  unfold problem_30_spec, input_list, output_list, is_positive.
  split.
  - (* is_subsequence output input *)
    simpl.
    right. right.
    left. split. reflexivity.
    left. split. reflexivity.
    left. split. reflexivity.
    trivial.
  - (* forall r, In r output <-> (In r input /\ r > 0) *)
    intro r.
    split.
    + (* In r output -> In r input /\ r > 0 *)
      intro H.
      simpl in H.
      destruct H as [H | [H | [H | H]]].
      * subst r. split.
        -- simpl. right. right. left. reflexivity.
        -- apply IZR_4_pos.
      * subst r. split.
        -- simpl. right. right. right. left. reflexivity.
        -- apply IZR_5_pos.
      * subst r. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- apply IZR_6_pos.
      * contradiction.
    + (* In r input /\ r > 0 -> In r output *)
      intro H.
      destruct H as [Hin Hpos].
      simpl in Hin.
      destruct Hin as [H | [H | [H | [H | [H | H]]]]].
      * subst r. exfalso. apply IZR_neg1_not_pos. exact Hpos.
      * subst r. exfalso. apply IZR_neg2_not_pos. exact Hpos.
      * subst r. simpl. left. reflexivity.
      * subst r. simpl. right. left. reflexivity.
      * subst r. simpl. right. right. left. reflexivity.
      * contradiction.
Qed.