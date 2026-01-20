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

Example test_intersperse: intersperse_spec [5%Z; 15%Z; 63%Z; 2%Z; (-2)%Z; 5%Z; 9%Z; 100%Z; 5%Z; (-9)%Z; 100%Z] 8%Z [5%Z; 8%Z; 15%Z; 8%Z; 63%Z; 8%Z; 2%Z; 8%Z; (-2)%Z; 8%Z; 5%Z; 8%Z; 9%Z; 8%Z; 100%Z; 8%Z; 5%Z; 8%Z; (-9)%Z; 8%Z; 100%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.