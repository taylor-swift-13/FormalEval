Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h x then 1 else 0) + count t x
  end.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if Z.geb (count l x) x then Z.max acc x else acc) (-1) l.

Example test_case_1 : search [2%Z; 2%Z; 3%Z; 4%Z; 10%Z; 4%Z; 5%Z; 7%Z; 5%Z; 3%Z] = 2%Z.
Proof. reflexivity. Qed.