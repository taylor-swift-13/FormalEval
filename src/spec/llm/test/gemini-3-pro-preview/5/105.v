Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Fixpoint intersperse (numbers : list Z) (delimeter : Z) : list Z :=
  match numbers with
  | [] => []
  | h :: [] => [h]
  | h :: t => h :: delimeter :: intersperse t delimeter
  end.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (res : list Z) : Prop :=
  res = intersperse numbers delimeter.

Example test_intersperse_1: intersperse_spec [9%Z; 3%Z] 6%Z [9%Z; 6%Z; 3%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.