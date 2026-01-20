Require Import Reals.
Require Import Floats.
Require Import Lra.
Require Import ZArith.
Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number > 0 /\
  exists (int_part : Z), 
    IZR int_part <= number < IZR (int_part + 1) /\
    result = number - IZR int_part /\
    0 <= result < 1.

Example test_truncate_number : truncate_number_spec 3.5 0.5.
Proof.
  unfold truncate_number_spec.
  split.
  - (* Prove number > 0 *)
    lra.
  - (* Instantiate the integer part with 3 *)
    exists 3%Z.
    split.
    + (* Verify 3 <= 3.5 < 4 *)
      split.
      * (* 3 <= 3.5 *)
        simpl.
        lra.
      * (* 3.5 < 4 *)
        simpl.
        lra.
    + split.
      * (* Verify result calculation: 0.5 = 3.5 - 3 *)
        simpl.
        lra.
      * (* Verify result range: 0 <= 0.5 < 1 *)
        lra.
Qed.