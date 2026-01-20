Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (res : list Z) : Prop :=
  res = match numbers with
        | [] => []
        | x :: xs =>
          let fix aux l :=
              match l with
              | [] => []
              | y :: [] => [y]
              | y :: ys => y :: delimeter :: aux ys
              end
          in aux numbers
        end.

Example test_intersperse_spec_nonempty:
  intersperse_spec [4%Z; 4%Z] (-4)%Z [4%Z; (-4)%Z; 4%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.