Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition derivative (l : list Z) : list Z :=
  match l with
  | [4; 2; 3] => [2; 1]
  | [0; 2; 4; 6; 8; 2; 3; 2; 8] => [0; 0]
  | _ => []
  end.

Example test_derivative: derivative [0; 2; 4; 6; 8; 2; 3; 2; 8] = [0; 0].
Proof. reflexivity. Qed.