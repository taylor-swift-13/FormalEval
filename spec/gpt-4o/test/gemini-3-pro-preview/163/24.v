Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

Example test_generate_integers : generate_integers_spec 201 9 [].
Proof.
  (* Unfold the definition of the specification *)
  unfold generate_integers_spec.
  
  (* 
     Simplify the expression. 
     1. The condition (201 <=? 9) evaluates to false, so we swap inputs: a=9, b=201.
     2. (b + 1) evaluates to 202.
     3. min 202 10 evaluates to 10.
     4. 10 - 9 evaluates to 1.
     5. seq 9 1 generates [9].
     6. filter keeps elements where (i mod 2 =? 0). 9 is odd, so result is [].
  *)
  vm_compute.
  
  (* Verify that the computed list equals the expected list *)
  reflexivity.
Qed.