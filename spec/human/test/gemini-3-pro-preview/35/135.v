Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [1; 3; 3; 5; 6; 6; 6; 8; 8; 9; 9; 9; 10; 10; 10; 12; 12; 13; 13; 13; 13; 13; 14; 14; 15; 15; 15; 17; 17; 18; 19; 20; 999997] 999997.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try lia; try contradiction.
Qed.