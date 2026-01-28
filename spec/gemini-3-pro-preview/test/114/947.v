Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.add 0 (filter (fun n => n <? x) xs)
  end.

Example test_case: solve [-4; 6; 5; -6; -8; 9; 4; -2; 2] = -14.
Proof. reflexivity. Qed.