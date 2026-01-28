Require Import Reals.
Require Import ZArith.
Require Import Psatz. (* Required for lra tactic *)
Require Import Floats.

Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number > 0 /\
  exists (int_part : Z), 
    IZR int_part <= number < IZR (int_part + 1) /\
    result = number - IZR int_part /\
    0 <= result < 1.

Example test_truncate_number : truncate_number_spec 8.24642675895752042 0.24642675895752042.
Proof.
  unfold truncate_number_spec.
  split.
  - (* Prove number > 0 *)
    lra.
  - (* Instantiate int_part with 8 *)
    exists 8%Z.
    repeat split.
    + (* Prove IZR 8 <= number *)
      simpl.
      lra.
    + (* Prove number < IZR (8 + 1) *)
      simpl.
      lra.
    + (* Prove result = number - IZR int_part *)
      simpl.
      lra.
    + (* Prove 0 <= result *)
      lra.
    + (* Prove result < 1 *)
      lra.
Qed.