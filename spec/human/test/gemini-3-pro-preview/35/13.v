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

Example test_case_35 : problem_35_spec [50; 49; 100; 48; 47; 46] 100.
Proof.
  unfold problem_35_spec.
  split.
  
  - (* Subgoal 1: Prove 100 is in the list *)
    simpl.
    tauto.
    
  - (* Subgoal 2: Prove that for any x in the list, x <= 100 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + lia. (* 50 <= 100 *)
    + lia. (* 49 <= 100 *)
    + lia. (* 100 <= 100 *)
    + lia. (* 48 <= 100 *)
    + lia. (* 47 <= 100 *)
    + lia. (* 46 <= 100 *)
    + contradiction.
Qed.