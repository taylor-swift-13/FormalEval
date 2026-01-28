Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.

Inductive Number :=
| NumZ : Z -> Number
| NumR : R -> Number.

Definition any_int_spec (x y z : Number) (result : bool) : Prop :=
  match x, y, z with
  | NumZ x, NumZ y, NumZ z =>
      result = (if Z.eq_dec x (y + z) then true else false) ||
               (if Z.eq_dec y (x + z) then true else false) ||
               (if Z.eq_dec z (x + y) then true else false)
  | _, _, _ => result = false
  end.

Example test_any_int : any_int_spec (NumR 3.0%R) (NumZ 4%Z) (NumZ 7%Z) false.
Proof.
  unfold any_int_spec.
  simpl.
  reflexivity.
Qed.