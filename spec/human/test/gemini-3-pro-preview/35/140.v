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

Example test_case_35 : problem_35_spec [3; 2; 2; 2; 2; 2] 3.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts:
     1. Prove 3 is in the list [3; 2; 2; 2; 2; 2].
     2. Prove that for any x in [3; 2; 2; 2; 2; 2], x <= 3. *)
  split.
  
  - (* Subgoal 1: In 3 [3; 2; 2; 2; 2; 2] *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x [3; 2; 2; 2; 2; 2] -> x <= 3 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* H : 3 = x \/ 2 = x \/ 2 = x \/ 2 = x \/ 2 = x \/ 2 = x \/ False *)
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* Case 3 = x *)
      lia.
    + (* Case 2 = x *)
      lia.
    + (* Case 2 = x *)
      lia.
    + (* Case 2 = x *)
      lia.
    + (* Case 2 = x *)
      lia.
    + (* Case 2 = x *)
      lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.