Require Import ZArith.
Open Scope Z_scope.

Fixpoint fibfib_iter (n : nat) (a b c : Z) : Z :=
  match n with
  | O => c
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  match n with
  | Z0 => 0
  | Zpos p => 
    if (p =? 1)%positive then 0
    else if (p =? 2)%positive then 1
    else fibfib_iter (Pos.to_nat p - 2) 0 0 1
  | Zneg _ => 0
  end.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example fibfib_test_case : fibfib_spec 63 8607945812375585.
Proof.
  unfold fibfib_spec.
  vm_compute.
  reflexivity.
Qed.