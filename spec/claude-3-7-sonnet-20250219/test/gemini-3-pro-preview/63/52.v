Require Import ZArith.
Open Scope Z_scope.

(* 
  The sequence is defined as:
  fibfib(0) = 0
  fibfib(1) = 0
  fibfib(2) = 1
  fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3) for n >= 3
  
  We implement a linear time tail-recursive helper to compute this efficiently.
  Working with Z is necessary because fibfib(34) = 181997601, which is too large for unary nat.
*)

Fixpoint fibfib_iter (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  fibfib_iter (Z.to_nat n) 0 0 1.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 34 181997601.
Proof.
  (* Using vm_compute to efficiently calculate the result on Z integers *)
  vm_compute.
  reflexivity.
Qed.