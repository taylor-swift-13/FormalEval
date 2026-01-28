Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => if Z.eq_dec x val then 1 + count val xs else count val xs
  end.

Definition search (l : list Z) : Z :=
  let p x := x <=? count x l in
  let candidates := filter p l in
  fold_left Z.max candidates (-1).

Example test_case_1: search [4%Z; 5%Z; 4%Z; 3%Z; 5%Z; 8%Z] = -1%Z.
Proof. reflexivity. Qed.