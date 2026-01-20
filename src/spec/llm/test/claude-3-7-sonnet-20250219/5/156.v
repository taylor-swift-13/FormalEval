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
  intersperse_spec [1; 1; 1; 2; 1] 0 [1; 0; 1; 0; 1; 0; 2; 0; 1].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.