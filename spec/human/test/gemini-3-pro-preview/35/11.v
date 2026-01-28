Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [2; 2; 2; 1; 2; 2] 2.
Proof.
  unfold problem_35_spec.
  split.
  - simpl.
    tauto.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + contradiction.
Qed.