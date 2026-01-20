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

Example test_intersperse: intersperse_spec [2%Z; 4%Z; 6%Z; 8%Z] 1%Z [2%Z; 1%Z; 4%Z; 1%Z; 6%Z; 1%Z; 8%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.