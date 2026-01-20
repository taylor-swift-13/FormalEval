Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x v then 1 else 0) + count v xs
  end.

Definition search (l : list Z) : Z :=
  fold_left (fun acc x => if count x l >=? x then Z.max acc x else acc) l (-1).

Example test_search: search [4%Z; 5%Z; 6%Z; 4%Z; 5%Z; 5%Z] = -1%Z.
Proof. reflexivity. Qed.