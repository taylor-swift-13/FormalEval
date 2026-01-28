Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

Example test_generate_integers : generate_integers_spec 2 1 [2].
Proof.
  (* Unfold the definition of the specification *)
  unfold generate_integers_spec.
  
  (* 
     Simplify the expression. 
     1. The condition (2 <=? 1) evaluates to false.
     2. Swap: a becomes 1, b becomes 2.
     3. (b + 1) evaluates to 3.
     4. min 3 10 evaluates to 3.
     5. 3 - 1 evaluates to 2.
     6. seq 1 2 generates [1; 2].
     7. filter keeps elements where (i mod 2 =? 0).
  *)
  vm_compute.
  
  (* Verify that the computed list equals the expected list *)
  reflexivity.
Qed.