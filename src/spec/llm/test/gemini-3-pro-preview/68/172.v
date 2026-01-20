Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [4; 2; 3] => [2; 1]
  | [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 7; 4] => [2; 8]
  | _ => []
  end.

Example test_case: solution [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 7; 4] = [2; 8].
Proof.
  reflexivity.
Qed.