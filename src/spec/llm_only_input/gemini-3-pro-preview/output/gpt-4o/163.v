Require Import List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.
Import Nat.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

Example test_generate_integers : generate_integers_spec 2 10 [2; 4; 6; 8].
Proof.
  (* Unfold the specification definition *)
  unfold generate_integers_spec.
  
  (* Simplify the expression. 
     This evaluates the 'if', the 'min', the subtraction, 
     the sequence generation, and the filter function 
     since all inputs are constant values. *)
  simpl.
  
  (* Prove that the left-hand side equals the right-hand side *)
  reflexivity.
Qed.