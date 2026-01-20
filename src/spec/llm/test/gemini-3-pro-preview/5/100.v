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

Example test_intersperse_complex: intersperse_spec 
  [15%Z; 63%Z; 2%Z; (-2)%Z; 5%Z; (-93)%Z; 100%Z; 5%Z; (-9)%Z] 
  9%Z 
  [15%Z; 9%Z; 63%Z; 9%Z; 2%Z; 9%Z; (-2)%Z; 9%Z; 5%Z; 9%Z; (-93)%Z; 9%Z; 100%Z; 9%Z; 5%Z; 9%Z; (-9)%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.