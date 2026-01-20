Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition max_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.max x xs
  end.

Definition solve (l : list Z) : Z :=
  sum_list l - max_list l.

Example test_case_1:
  solve [100000; -50000; 50000; -100000; -9; -50000; 50000; -100000; 100000; -50000; 50000; 100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000; -100000] = -200009.
Proof.
  reflexivity.
Qed.