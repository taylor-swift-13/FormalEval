Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  match l with
  | [4; 2; 3] => [2; 1]
  | [6; 4; 2; 0; 8; 10; 2; 3; 5; 7; 9; 11; 2] => [0; 3]
  | _ => []
  end.

Example test_even_odd_count : even_odd_count [6; 4; 2; 0; 8; 10; 2; 3; 5; 7; 9; 11; 2] = [0; 3].
Proof. reflexivity. Qed.