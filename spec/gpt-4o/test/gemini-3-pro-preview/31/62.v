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

Example test_is_prime_neg_7 : is_prime_spec (-7) false.
Proof.
  (* Unfold the specification *)
  unfold is_prime_spec.
  
  (* Split the main conjunctions *)
  split.
  - (* Case: n <= 1 *)
    intros H_le.
    (* -7 <= 1 is true, so we need to prove false = false *)
    reflexivity.
    
  - (* Case: n > 1 *)
    intros H_gt.
    (* -7 > 1 is false, contradiction *)
    lia.
Qed.