Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Definition solution (l : list Z) : Z :=
  let m := min_list l in
  fold_right (fun x acc => if Z.eqb x m then x + acc else acc) 0 l.

Example test_case : solution [1%Z; -2%Z; 3%Z; -4%Z; -1%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -10%Z; -10%Z; -10%Z] = -40%Z.
Proof. reflexivity. Qed.