Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (n : Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => Z.geb (count l x) x) l in
  match filtered with
  | [] => -1
  | x :: xs => fold_right Z.min x xs
  end.

Example search_example : search [-1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; 30%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z] = -1%Z.
Proof. reflexivity. Qed.