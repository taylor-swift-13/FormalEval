Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

Example test_generate_integers : generate_integers_spec 15 16 [].
Proof.
  (* Unfold the definition of the specification *)
  unfold generate_integers_spec.
  
  (* 
     Simplify the expression. 
     1. The condition (15 <=? 16) evaluates to true.
     2. (b + 1) evaluates to 17.
     3. min 17 10 evaluates to 10.
     4. 10 - 15 evaluates to 0 (in natural number arithmetic).
     5. seq 15 0 generates [].
     6. filter on an empty list returns [].
  *)
  vm_compute.
  
  (* Verify that the computed list equals the expected list *)
  reflexivity.
Qed.