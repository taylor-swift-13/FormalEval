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

Example test_truncate_number : truncate_number_spec 2.333802704974898 0.333802704974898.
Proof.
  unfold truncate_number_spec.
  split.
  - (* Prove number > 0 *)
    lra.
  - (* Instantiate int_part with 2 *)
    exists 2%Z.
    repeat split.
    + (* Prove IZR 2 <= 2.333... *)
      simpl.
      lra.
    + (* Prove 2.333... < IZR (2 + 1) *)
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