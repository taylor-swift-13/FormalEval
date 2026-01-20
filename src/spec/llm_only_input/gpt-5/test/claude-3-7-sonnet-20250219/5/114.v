Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

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

Example intersperse_spec_test_nonempty :
  intersperse_spec [1%nat; 2%nat; 3%nat; 4%nat; 1%nat] (Z.to_nat 0%Z) [1%nat; 0%nat; 2%nat; 0%nat; 3%nat; 0%nat; 4%nat; 0%nat; 1%nat].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.