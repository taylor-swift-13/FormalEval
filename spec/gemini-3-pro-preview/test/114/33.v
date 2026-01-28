Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example example : solve [-10; 4; 5; 3; -2; 0; 4; -8] = -10.
Proof.
  reflexivity.
Qed.