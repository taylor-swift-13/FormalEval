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

Example test_intersperse_new: intersperse_spec [-1; 1; -2; -2; -3] 10000 [-1; 10000; 1; 10000; -2; 10000; -2; 10000; -3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.