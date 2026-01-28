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

Example test_case_35 : problem_35_spec [-5; -6; -5; -5; -5; -5; -5] (-5).
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts:
     1. Prove -5 is in the list.
     2. Prove that for any x in the list, x <= -5. *)
  split.
  
  - (* Subgoal 1: In -5 input *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x input -> x <= -5 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* H is a large disjunction of equalities or False. 
       We use repeat destruct to handle the list length dynamically 
       and try to solve each case with lia or contradiction. *)
    repeat destruct H as [H | H]; try lia; try contradiction.
Qed.