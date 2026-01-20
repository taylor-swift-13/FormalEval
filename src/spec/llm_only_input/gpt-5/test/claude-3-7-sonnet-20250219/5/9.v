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

Example intersperse_spec_test :
  intersperse_spec (map Z.to_nat [1%Z; 3%Z; 5%Z; 7%Z]) (Z.to_nat 4%Z) (map Z.to_nat [1%Z; 4%Z; 3%Z; 4%Z; 5%Z; 4%Z; 7%Z]).
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.