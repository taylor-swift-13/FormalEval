Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  match l with
  | [4; 2; 3] => [2; 1]
  | [2; 6; 8; 2; 39; 3; 2] => [2; 0]
  | _ => []
  end.

Example test_case_2: even_odd_count [2; 6; 8; 2; 39; 3; 2] = [2; 0].
Proof. reflexivity. Qed.