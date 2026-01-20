Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_list_aux (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | x :: xs => min_list_aux xs (Z.min x acc)
  end.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => min_list_aux xs x
  end.

Definition solution (l : list Z) : Z :=
  let m := min_list l in
  if m <? 0 then m - 1 else m.

Example test_case: solution [1%Z; 0%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 90%Z; -1%Z; -2%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -3%Z.
Proof. reflexivity. Qed.