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

Example test_is_prime_1009 : is_prime_spec 1009 true.
Proof.
  (* Unfold the specification *)
  unfold is_prime_spec.
  
  (* Split the main conjunctions *)
  split.
  - (* Case: n <= 1 *)
    intros H_le.
    (* 1009 <= 1 is a contradiction *)
    lia.
    
  - (* Case: n > 1 *)
    intros H_gt.
    split.
    + (* Sub-case: If a divisor exists, result is false *)
      intros [i [H_bounds H_div]].
      (* The goal is true = false. We must show that the hypothesis (existence of a divisor) is false.
         We verify by computation that no number in [2, 1008] divides 1009. *)
      
      (* Define a checker function that returns true if i does NOT divide 1009 *)
      pose (check := fun x => negb (1009 mod x =? 0)).
      
      (* Verify that this check passes for all numbers in the range [2, 1008] *)
      assert (H_all: forallb check (seq 2 1007) = true).
      { vm_compute. reflexivity. }
      
      (* Map the boolean check back to the logical quantifier *)
      rewrite forallb_forall in H_all.
      
      (* Show that the witness i is in the checked range *)
      assert (H_in: In i (seq 2 1007)).
      { apply in_seq. lia. }
      
      (* Apply the check to i *)
      specialize (H_all i H_in).
      unfold check in H_all.
      
      (* Use the hypothesis that i divides 1009 to derive a contradiction *)
      rewrite H_div in H_all.
      simpl in H_all.
      discriminate.
      
    + (* Sub-case: If no divisor exists, result is true *)
      intros H_forall.
      (* The goal is true = true, which is trivial *)
      reflexivity.
Qed.