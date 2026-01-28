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

Example test_intersperse_complex: intersperse_spec [7; 1; 1; 1; 1; 1] (-5) [7; -5; 1; -5; 1; -5; 1; -5; 1; -5; 1].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.