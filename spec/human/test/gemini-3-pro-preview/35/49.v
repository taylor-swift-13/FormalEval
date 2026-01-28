Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [8; 6; 6; 4; 3; 98; 8] 98.
Proof.
  unfold problem_35_spec.
  split.
  
  - (* Subgoal 1: In 98 [8; 6; 6; 4; 3; 98; 8] *)
    simpl.
    tauto.
    
  - (* Subgoal 2: forall x, In x [8; 6; 6; 4; 3; 98; 8] -> x <= 98 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + contradiction.
Qed.