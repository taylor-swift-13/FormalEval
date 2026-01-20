Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eq_dec y x then 1 else 0) + count tl x
  end.

Definition search (l : list Z) : Z :=
  let unique := nodup Z.eq_dec l in
  let valid := filter (fun x => Z.leb x (count l x)) unique in
  fold_left Z.max valid (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 14%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 1%Z; 3%Z] = 3%Z.
Proof. reflexivity. Qed.