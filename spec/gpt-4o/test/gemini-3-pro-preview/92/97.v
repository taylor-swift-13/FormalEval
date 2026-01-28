Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = (if Z.eq_dec x (y + z) then true else false) ||
           (if Z.eq_dec y (x + z) then true else false) ||
           (if Z.eq_dec z (x + y) then true else false).

Example test_any_int : any_int_spec (-1)%Z (-31)%Z (-1)%Z false.
Proof.
  unfold any_int_spec.
  simpl.
  reflexivity.
Qed.