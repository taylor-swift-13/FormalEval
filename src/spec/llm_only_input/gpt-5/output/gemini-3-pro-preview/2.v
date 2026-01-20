Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number >= 0 ->
  exists i : Z, IZR i <= number < IZR i + 1 /\ result = number - IZR i.

Example truncate_number_spec_example_3_5 :
  truncate_number_spec 3.5%R 0.5%R.
Proof.
  unfold truncate_number_spec.
  intros Hnonneg.
  exists 3%Z.
  split.
  - split; simpl; lra.
  - simpl; lra.
Qed.