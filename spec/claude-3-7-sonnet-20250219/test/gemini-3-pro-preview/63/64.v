Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Fixpoint fibfib_iter (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S k => fibfib_iter k b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  match n with
  | Z.pos p => fibfib_iter (Pos.to_nat p) 0 0 1
  | _ => 0
  end.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example fibfib_test_case : fibfib_spec 99 28992087708416717612934417.
Proof.
  unfold fibfib_spec.
  vm_compute.
  reflexivity.
Qed.