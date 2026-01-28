Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_zeros (l : list Z) : Z :=
  fold_right (fun x acc => if x =? 0 then acc + 1 else acc) 0 l.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => fold_right Z.min h t
  end.

Definition solution (l : list Z) : Z :=
  min_list l - count_zeros l.

Example test_case: solution [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 90%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -70%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 0%Z; 1%Z] = -72%Z.
Proof. reflexivity. Qed.