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

Example test_intersperse_numbers: intersperse_spec [1%Z; 2%Z; 3%Z; 4%Z] 9999%Z [1%Z; 9999%Z; 2%Z; 9999%Z; 3%Z; 9999%Z; 4%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.