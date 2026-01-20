Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h x then 1 else 0) + count t x
  end.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if count l x >=? x then Z.max acc x else acc) (-1) l.

Example search_example_1:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 7%Z; 9%Z; 10%Z; 10%Z; 10%Z; 1%Z] = 4%Z.
Proof. reflexivity. Qed.