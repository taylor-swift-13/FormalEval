Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_test_case :
  problem_35_spec [3%Z; 6%Z; 0%Z] 6%Z.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. right. left. reflexivity.
  - intros x H. simpl in H. destruct H as [H | [H | [H | H]]]; subst; auto with zarith.
Qed.