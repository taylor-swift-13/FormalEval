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

Example test_case_35 : problem_35_spec [100; 100] 100.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts:
     1. Prove 100 is in the list [100; 100].
     2. Prove that for any x in [100; 100], x <= 100. *)
  split.
  
  - (* Subgoal 1: In 100 [100; 100] *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x [100; 100] -> x <= 100 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* H : 100 = x \/ 100 = x \/ False *)
    destruct H as [H | [H | H]].
    + (* Case 100 = x *)
      lia. (* Solves linear integer arithmetic: if 100 = x then x <= 100 *)
    + (* Case 100 = x *)
      lia. (* if 100 = x then x <= 100 *)
    + (* Case False (end of list) *)
      contradiction.
Qed.