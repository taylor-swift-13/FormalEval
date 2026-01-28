Require Import ZArith.
Require Import List.
Require Import Lia.
Open Scope Z_scope.

Definition fib4_step (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
  let '(a, b, c, d) := st in
  (b, c, d, a + b + c + d).

Definition fib4_spec (n : Z) (result : Z) : Prop :=
  (n = 0 /\ result = 0) \/
  (n = 1 /\ result = 0) \/
  (n = 2 /\ result = 2) \/
  (n = 3 /\ result = 0) \/
  (n >= 4 /\
   let count := Z.to_nat (n - 3) in
   let '(_, _, _, d) := Nat.iter count fib4_step (0, 0, 2, 0) in
   result = d).

Example fib4_test : fib4_spec 93 47011480492525468175029672.
Proof.
  unfold fib4_spec.
  repeat right.
  split.
  - lia.
  - vm_compute. reflexivity.
Qed.