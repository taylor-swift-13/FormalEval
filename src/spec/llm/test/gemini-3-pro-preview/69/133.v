Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eq_dec x h then 1 + count x t else count x t
  end.

Definition search (l : list Z) : Z :=
  let p x := count x l >=? x in
  fold_left Z.max (filter p l) (-1).

Example test_search: search [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10] = 5.
Proof. reflexivity. Qed.