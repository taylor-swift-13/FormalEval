Require Import Coq.Lists.List.
Import ListNotations.

Definition intersperse_spec (numbers : list nat) (delimeter : nat) (res : list nat) : Prop :=
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
  intersperse_spec [1; 2; 3] 4 [1; 4; 2; 4; 3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.