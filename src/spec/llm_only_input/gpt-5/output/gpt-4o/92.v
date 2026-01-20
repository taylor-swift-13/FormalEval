Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = (if Z.eq_dec x (y + z) then true else false) ||
           (if Z.eq_dec y (x + z) then true else false) ||
           (if Z.eq_dec z (x + y) then true else false).

Example any_int_spec_test :
  any_int_spec 2%Z 3%Z 1%Z true.
Proof.
  unfold any_int_spec.
  vm_compute.
  reflexivity.
Qed.