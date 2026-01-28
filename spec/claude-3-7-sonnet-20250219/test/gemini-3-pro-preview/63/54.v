Require Import ZArith.
Open Scope Z_scope.

(* 
   The problem asks for the 45th element of the Tribonacci sequence (fibfib).
   Sequence: f(0)=0, f(1)=0, f(2)=1, f(n) = f(n-1) + f(n-2) + f(n-3).
   
   Since the target value is large (approx 1.48e11), we must use Z (binary integers) 
   instead of nat (unary) to avoid stack overflow and timeouts during verification.
*)

(* Tail-recursive helper to compute Tribonacci numbers efficiently *)
Fixpoint fibfib_iter (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

(* Main definition converting Z input to nat for recursion depth *)
Definition fibfib (n : Z) : Z :=
  fibfib_iter (Z.to_nat n) 0 0 1.

(* Specification simply asserts the result matches the function *)
Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example fibfib_test_case : fibfib_spec 45 148323355432.
Proof.
  unfold fibfib_spec.
  (* vm_compute is required to handle the large integer arithmetic efficiently *)
  vm_compute.
  reflexivity.
Qed.