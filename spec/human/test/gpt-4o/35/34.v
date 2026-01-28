Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_test_case :
  problem_35_spec [3%Z; 1%Z; 2%Z; 9%Z; 4%Z; 5%Z; 6%Z; 7%Z; 5%Z; 5%Z] 9%Z.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. right. right. right. left. reflexivity.
  - intros x H. simpl in H. 
    repeat (destruct H as [H | H]; subst; try solve [auto with zarith]).
Qed.