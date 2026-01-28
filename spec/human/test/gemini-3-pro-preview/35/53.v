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

Example test_case_35 : problem_35_spec [2; 2; 3; 2; 47; 2; 2] 47.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts *)
  split.
  
  - (* Subgoal 1: In 47 [2; 2; 3; 2; 47; 2; 2] *)
    simpl. (* Simplifies In to a disjunction of equalities *)
    tauto. (* Automatically solves the tautology *)
    
  - (* Subgoal 2: forall x, In x [2; 2; 3; 2; 47; 2; 2] -> x <= 47 *)
    intros x H.
    simpl in H. (* Simplifies the hypothesis H into disjunctions *)
    (* Repeatedly destruct the disjunctions and solve with lia *)
    repeat (destruct H as [H | H]; [lia | ]).
    contradiction.
Qed.