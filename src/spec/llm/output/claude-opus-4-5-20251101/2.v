Require Import Reals.
Require Import Floats.
Require Import ZArith.
Require Import Lra.
Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number > 0 /\
  exists (int_part : Z), 
    IZR int_part <= number < IZR (int_part + 1) /\
    result = number - IZR int_part /\
    0 <= result < 1.

(* Define 3.5 and 0.5 *)
Definition R3_5 : R := 3 + /2.
Definition R0_5 : R := /2.

Example truncate_test : truncate_number_spec R3_5 R0_5.
Proof.
  unfold truncate_number_spec, R3_5, R0_5.
  split.
  - (* 3.5 > 0 *)
    lra.
  - (* exists int_part *)
    exists 3%Z.
    split.
    + (* IZR 3 <= 3.5 < IZR 4 *)
      simpl.
      split; lra.
    + split.
      * (* 0.5 = 3.5 - 3 *)
        simpl. lra.
      * (* 0 <= 0.5 < 1 *)
        lra.
Qed.