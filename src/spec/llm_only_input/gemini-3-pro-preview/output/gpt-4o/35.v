Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (max_elem : nat) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [1; 2; 3] 3.
Proof.
  (* Unfold the specification definition *)
  unfold max_element_spec.
  
  (* Split the conjunction into two subgoals:
     1. 3 is in the list
     2. For all x in the list, x <= 3 *)
  split.
  
  - (* Subgoal 1: In 3 [1; 2; 3] *)
    simpl. (* Reduces In to a sequence of disjunctions *)
    right. right. left. (* Navigate to 3 = 3 *)
    reflexivity.
    
  - (* Subgoal 2: forall x, In x [1; 2; 3] -> x <= 3 *)
    intros x H.
    simpl in H. (* Unfold In in the hypothesis *)
    
    (* Destruct the hypothesis H to handle each element in the list *)
    destruct H as [H1 | [H2 | [H3 | H4]]].
    
    + (* Case x = 1 *)
      rewrite H1.
      lia. (* 1 <= 3 is true by linear integer arithmetic *)
      
    + (* Case x = 2 *)
      rewrite H2.
      lia. (* 2 <= 3 is true *)
      
    + (* Case x = 3 *)
      rewrite H3.
      lia. (* 3 <= 3 is true *)
      
    + (* Case False (empty tail) *)
      contradiction.
Qed.