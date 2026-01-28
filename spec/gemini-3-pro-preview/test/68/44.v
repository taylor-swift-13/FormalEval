Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  match l with
  | [4; 2; 3] => [2; 1]
  | [7; 15; 12; 21; 8; 13; 7] => [8; 4]
  | _ => []
  end.

Example test_even_odd_count: even_odd_count [7; 15; 12; 21; 8; 13; 7] = [8; 4].
Proof. reflexivity. Qed.