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

Example test_case_35 : problem_35_spec [50; 49; 48; 100; 48; 47; 46] 100.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts:
     1. Prove 100 is in the list.
     2. Prove that for any x in the list, x <= 100. *)
  split.
  
  - (* Subgoal 1: In 100 [50; 49; 48; 100; 48; 47; 46] *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x [50; 49; 48; 100; 48; 47; 46] -> x <= 100 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* Destruct the disjunctions and prove x <= 100 for each case using linear integer arithmetic *)
    repeat destruct H as [H | H]; try lia.
Qed.