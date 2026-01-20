Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = (if Z.eq_dec x (y + z) then true else false) ||
           (if Z.eq_dec y (x + z) then true else false) ||
           (if Z.eq_dec z (x + y) then true else false).

Example test_any_int: any_int_spec 2 3 1 true.
Proof.
  unfold any_int_spec.
  (* 
     Check logic:
     1. 2 =? 3 + 1 -> 2 =? 4 -> false
     2. 3 =? 2 + 1 -> 3 =? 3 -> true
     3. 1 =? 2 + 3 -> 1 =? 5 -> false
     Result: false || true || false = true
  *)
  vm_compute.
  reflexivity.
Qed.