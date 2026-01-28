Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Note: The specification provided in the description contained ambiguity 
   regarding the scope of quantifiers and implication. 
   Parentheses have been added to the hypotheses of the implications 
   to ensure the logical definition of primality is correct and provable. *)

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 ->
   ((exists i, 2 <= i < n /\ n mod i = 0) -> result = false) /\
   ((forall i, 2 <= i < n -> n mod i <> 0) -> result = true)).

Example test_is_prime_neg_5 : is_prime_spec (-5) false.
Proof.
  (* Unfold the specification *)
  unfold is_prime_spec.
  
  (* Split the main conjunctions *)
  split.
  - (* Case: n <= 1 *)
    intros H_le.
    (* -5 <= 1 is true, so we must show result = false.
       The goal is false = false, which is trivial. *)
    reflexivity.
    
  - (* Case: n > 1 *)
    intros H_gt.
    (* -5 > 1 is a contradiction *)
    lia.
Qed.