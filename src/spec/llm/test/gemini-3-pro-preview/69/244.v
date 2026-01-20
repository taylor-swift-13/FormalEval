Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (v : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x v then acc + 1 else acc) 0 l.

Fixpoint search_aux (n : nat) (l : list Z) : Z :=
  match n with
  | O => -1
  | S n' => 
      let z := Z.of_nat n in
      if z <=? count z l then z else search_aux n' l
  end.

Definition search (l : list Z) : Z :=
  search_aux (length l) l.

Example test_case_1: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 9%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 5%Z; 1%Z; 3%Z] = 3%Z.
Proof. compute. reflexivity. Qed.