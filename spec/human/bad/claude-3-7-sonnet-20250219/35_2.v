Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_example :
  problem_35_spec [5; 3; -5; 2; -3; 3; 9; 0; 124; 1; -10] 124.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. 
    repeat (right).
    left.
    reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H
      | [H
      | [H
      | [H
      | [H
      | [H
      | [H
      | [H
      | [H
      | [H
      | H] ] ] ] ] ] ] ] ].
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
Qed.