Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz. (* Imports lia tactic for integer arithmetic *)
Import ListNotations.
Open Scope Z_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [1; 3; 3; 5; 6; 6; 6; 8; 8; 9; 9; 9; 9; 10; 10; 10; 12; 12; 13; 13; 13; 13; 13; 14; 14; 15; 15; 17; 17; 18; 19; 20; 3] 20.
Proof.
  unfold problem_35_spec.
  split.
  
  - (* Subgoal 1: In 20 input *)
    simpl.
    tauto.
    
  - (* Subgoal 2: forall x, In x input -> x <= 20 *)
    intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try lia.
Qed.