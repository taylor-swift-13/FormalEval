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
  intersperse_spec [4; 1; 2; 3; 3; 18446744073709551611] 10000 [4; 10000; 1; 10000; 2; 10000; 3; 10000; 3; 10000; 18446744073709551611].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.