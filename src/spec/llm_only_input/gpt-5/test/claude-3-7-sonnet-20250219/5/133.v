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

Example intersperse_spec_test_case :
  intersperse_spec (map Z.to_nat [3%Z; 2%Z; 3%Z; 4%Z]) (Z.to_nat 10000%Z) (map Z.to_nat [3%Z; 10000%Z; 2%Z; 10000%Z; 3%Z; 10000%Z; 4%Z]).
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.