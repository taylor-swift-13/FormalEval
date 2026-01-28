Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

(* Note: The specification provided in the description contained ambiguity 
   regarding the scope of quantifiers and implication. 
   Parentheses have been added to the hypotheses of the implications 
   to ensure the logical definition of primality is correct and provable. *)

Definition is_prime_spec (n : nat) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 ->
   ((exists i, 2 <= i < n /\ n mod i = 0) -> result = false) /\
   ((forall i, 2 <= i < n -> n mod i <> 0) -> result = true)).

Example test_is_prime_85 : is_prime_spec 85 false.
Proof.
  (* Unfold the specification *)
  unfold is_prime_spec.
  
  (* Split the main conjunctions *)
  split.
  - (* Case: n <= 1 *)
    intros H_le.
    (* 85 <= 1 is a contradiction *)
    lia.
    
  - (* Case: n > 1 *)
    intros H_gt.
    split.
    + (* Sub-case: If a divisor exists, result is false *)
      intros H_exists.
      (* The goal is false = false, which is trivial *)
      reflexivity.
      
    + (* Sub-case: If no divisor exists, result is true *)
      intros H_forall.
      (* We must show that the hypothesis H_forall (that 85 is prime) is false.
         We do this by exhibiting a witness (5) that divides 85. *)
      assert (H_bounds : 2 <= 5 < 85). { lia. }
      
      (* Apply the bounds to the hypothesis *)
      specialize (H_forall 5 H_bounds).
      
      (* Simplify 85 mod 5 to 0 *)
      simpl in H_forall.
      
      (* H_forall is now "0 <> 0", which is a contradiction *)
      contradiction.
Qed.