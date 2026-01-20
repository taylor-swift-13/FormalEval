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

Example test_intersperse_basic: intersperse_spec [1%Z; 3%Z; 4%Z] 10000%Z [1%Z; 10000%Z; 3%Z; 10000%Z; 4%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.