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

Example test_case_35 : problem_35_spec [100; 100; 99; 98; 97] 100.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts:
     1. Prove 100 is in the list [100; 100; 99; 98; 97].
     2. Prove that for any x in the list, x <= 100. *)
  split.
  
  - (* Subgoal 1: In 100 [100; 100; 99; 98; 97] *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x [100; 100; 99; 98; 97] -> x <= 100 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* H : 100 = x \/ 100 = x \/ 99 = x \/ 98 = x \/ 97 = x \/ False *)
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + (* Case 100 = x *)
      lia. 
    + (* Case 100 = x *)
      lia. 
    + (* Case 99 = x *)
      lia. 
    + (* Case 98 = x *)
      lia. 
    + (* Case 97 = x *)
      lia. 
    + (* Case False (end of list) *)
      contradiction.
Qed.