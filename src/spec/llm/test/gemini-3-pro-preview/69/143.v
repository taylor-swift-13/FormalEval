Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if v =? x then 1 else 0) + count v xs
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x =? count x l) l in
  fold_left Z.max candidates (-1).

Example search_example: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 10%Z; 5%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] = 5%Z.
Proof. reflexivity. Qed.