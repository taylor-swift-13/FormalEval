Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_test_case :
  problem_35_spec [101%Z; 100%Z; 100%Z] 101%Z.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. left. reflexivity.
  - intros x H. simpl in H. destruct H as [H | [H | [H | H]]]; subst; auto with zarith.
Qed.