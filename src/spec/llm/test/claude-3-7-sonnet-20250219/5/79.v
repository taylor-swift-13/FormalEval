Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.

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
  intersperse_spec [-2; 7; 2; 1; 9] 2 [-2; 2; 7; 2; 2; 2; 1; 2; 9].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.