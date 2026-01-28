Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x target then 1 else 0) + count target xs
  end.

Definition search (l : list Z) : Z :=
  let p x := count x l >=? x in
  fold_left Z.max (filter p l) (-1).

Example test_search: search [2; 2; 3; 4; 4; 4; 5; 7; 5; 5] = 2.
Proof. reflexivity. Qed.