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

Definition R11_020840370441608 : R := 11020840370441608 / 1000000000000000.
Definition R0_020840370441607803 : R := 20840370441607803 / 1000000000000000000.

Example truncate_test : truncate_number_spec R11_020840370441608 (R11_020840370441608 - 11).
Proof.
  unfold truncate_number_spec, R11_020840370441608.
  split.
  - lra.
  - exists 11%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * ring.
      * simpl. lra.
Qed.