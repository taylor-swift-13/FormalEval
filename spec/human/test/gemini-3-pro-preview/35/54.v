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

Example test_case_35_2 : problem_35_spec [-1; 5; -3; -4; 0] 5.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts:
     1. Prove 5 is in the list [-1; 5; -3; -4; 0].
     2. Prove that for any x in [-1; 5; -3; -4; 0], x <= 5. *)
  split.
  
  - (* Subgoal 1: In 5 [-1; 5; -3; -4; 0] *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x [-1; 5; -3; -4; 0] -> x <= 5 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* H : -1 = x \/ 5 = x \/ -3 = x \/ -4 = x \/ 0 = x \/ False *)
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + (* Case -1 = x *)
      lia.
    + (* Case 5 = x *)
      lia.
    + (* Case -3 = x *)
      lia.
    + (* Case -4 = x *)
      lia.
    + (* Case 0 = x *)
      lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.