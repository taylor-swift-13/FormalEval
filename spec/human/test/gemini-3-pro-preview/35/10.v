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

Example test_case_35 : problem_35_spec [1; 1; 1; 1] 1.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts:
     1. Prove 1 is in the list [1; 1; 1; 1].
     2. Prove that for any x in [1; 1; 1; 1], x <= 1. *)
  split.
  
  - (* Subgoal 1: In 1 [1; 1; 1; 1] *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x [1; 1; 1; 1] -> x <= 1 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* H : 1 = x \/ 1 = x \/ 1 = x \/ 1 = x \/ False *)
    destruct H as [H | [H | [H | [H | H]]]].
    + (* Case 1 = x *)
      lia. 
    + (* Case 1 = x *)
      lia. 
    + (* Case 1 = x *)
      lia. 
    + (* Case 1 = x *)
      lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.