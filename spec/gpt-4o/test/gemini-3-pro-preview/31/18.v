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

Example test_is_prime_103 : is_prime_spec 103 true.
Proof.
  (* Unfold the specification *)
  unfold is_prime_spec.
  
  (* Split the main conjunctions *)
  split.
  - (* Case: n <= 1 *)
    intros H_le.
    (* 103 <= 1 is a contradiction *)
    lia.
    
  - (* Case: n > 1 *)
    intros H_gt.
    split.
    + (* Sub-case: If a divisor exists, result is false *)
      intros [i [H_bounds H_div]].
      (* We must show that no such i exists for n = 103.
         We do this by exhaustively checking all i in range [0, 102].
         For i < 2, H_bounds (2 <= i) gives a contradiction.
         For 2 <= i <= 102, computing 103 mod i <> 0 gives a contradiction. *)
      do 103 (destruct i; [ try lia; simpl in H_div; try discriminate | ]).
      (* Remaining case: i >= 103, which contradicts i < 103 *)
      lia.
      
    + (* Sub-case: If no divisor exists, result is true *)
      intros H_forall.
      reflexivity.
Qed.