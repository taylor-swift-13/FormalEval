Require Import Arith.Arith.
Require Import ZArith.

Open Scope Z_scope.

Fixpoint fibfib_aux (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S n' => fibfib_aux n' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  match n with
  | Z0 => 0
  | Zpos p => fibfib_aux (Pos.to_nat p) 0 0 1
  | Zneg _ => 0
  end.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example fibfib_test_case : fibfib_spec 57 222332455004452.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.