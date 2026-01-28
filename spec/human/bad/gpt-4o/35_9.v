Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.

Definition problem_35_pre (input : list Q) : Prop := input <> []%list.

Definition problem_35_spec (input : list Q) (output : Q) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Q.

Example problem_35_test_case :
  problem_35_spec [1.5#1; 3#1; 2#1; -4#1; -3.5#1; 0#1; 2.5#1] 3#1.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. right. left. reflexivity.
  - intros x H. simpl in H. destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst; auto with qarith.
Qed.