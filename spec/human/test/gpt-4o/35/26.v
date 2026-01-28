Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_test_case :
  problem_35_spec [8%Z; 6%Z; 6%Z; 4%Z; 6%Z; 3%Z] 8%Z.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. left. reflexivity.
  - intros x H. simpl in H. destruct H as [H | [H | [H | [H | [H | [H | H]]]]]]; subst; auto with zarith.
Qed.