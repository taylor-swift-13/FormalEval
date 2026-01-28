Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (z : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => if Z.eq_dec x z then 1 + count_occ z xs else count_occ z xs
  end.

Definition search (l : list Z) : Z :=
  fold_left (fun acc x => if count_occ x l >=? x then Z.max acc x else acc) l (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] = 4%Z.
Proof. reflexivity. Qed.