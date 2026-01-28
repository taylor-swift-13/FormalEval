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

Example test_intersperse_complex: intersperse_spec [0%Z; 0%Z; 0%Z; (-1)%Z] 7%Z [0%Z; 7%Z; 0%Z; 7%Z; 0%Z; 7%Z; (-1)%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.