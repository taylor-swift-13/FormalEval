Require Import ZArith.
Open Scope Z_scope.

Fixpoint fibfib_iter (k : nat) (a b c : Z) : Z :=
  match k with
  | O => c
  | S k' => fibfib_iter k' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  if n =? 0 then 0
  else if n =? 1 then 0
  else fibfib_iter (Z.to_nat (n - 2)) 0 0 1.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 60 1383410902447554.
Proof.
  reflexivity.
Qed.