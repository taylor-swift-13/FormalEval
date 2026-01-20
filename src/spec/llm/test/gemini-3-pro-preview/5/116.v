Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint intersperse (numbers : list Z) (delimeter : Z) : list Z :=
  match numbers with
  | [] => []
  | h :: [] => [h]
  | h :: t => h :: delimeter :: intersperse t delimeter
  end.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (res : list Z) : Prop :=
  res = intersperse numbers delimeter.

Example test_intersperse_new: intersperse_spec [7; 3; 6; 8; 4; 2; 1; 3] (-1) [7; -1; 3; -1; 6; -1; 8; -1; 4; -1; 2; -1; 1; -1; 3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.