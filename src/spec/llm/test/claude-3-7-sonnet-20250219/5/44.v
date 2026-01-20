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

Example test_intersperse_spec_full:
  intersperse_spec [3%nat; 6%nat; 2%nat; 5%nat; 1%nat; 9%nat] 1%nat [3%nat; 1%nat; 6%nat; 1%nat; 2%nat; 1%nat; 5%nat; 1%nat; 1%nat; 1%nat; 9%nat].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.