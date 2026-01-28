Require Import ZArith.
Open Scope Z_scope.

Definition fibfib (n : Z) : Z :=
  let fix iter (k : nat) (a b c : Z) :=
    match k with
    | O => a
    | S k' => iter k' b c (a + b + c)
    end
  in
  if n <? 0 then 0 else iter (Z.to_nat n) 0 0 1.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 43 43844049029.
Proof.
  unfold fibfib_spec.
  vm_compute.
  reflexivity.
Qed.