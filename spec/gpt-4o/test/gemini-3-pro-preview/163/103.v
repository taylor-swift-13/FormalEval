Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

Example test_generate_integers : generate_integers_spec 8 298 [8].
Proof.
  (* Unfold the definition of the specification *)
  unfold generate_integers_spec.
  
  (* 
     Simplify the expression. 
     1. The condition (8 <=? 298) evaluates to true.
     2. (b + 1) evaluates to 299.
     3. min 299 10 evaluates to 10.
     4. 10 - 8 evaluates to 2.
     5. seq 8 2 generates [8; 9].
     6. filter keeps elements where (i mod 2 =? 0), resulting in [8].
  *)
  vm_compute.
  
  (* Verify that the computed list equals the expected list *)
  reflexivity.
Qed.