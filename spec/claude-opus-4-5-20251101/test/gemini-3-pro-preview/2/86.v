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

Example test_truncate_number : truncate_number_spec 3.3212272614517486 0.3212272614517486.
Proof.
  unfold truncate_number_spec.
  split.
  - 
    lra.
  - 
    exists 3%Z.
    repeat split.
    + 
      simpl.
      lra.
    + 
      simpl.
      lra.
    + 
      simpl.
      lra.
    + 
      lra.
    + 
      lra.
Qed.