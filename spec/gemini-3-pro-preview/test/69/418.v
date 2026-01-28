Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eq_dec h x then 1 + count x t else count x t
  end.

Definition search (l : list Z) : Z :=
  let fix aux (rem : list Z) (acc : Z) : Z :=
    match rem with
    | [] => acc
    | h :: t =>
      if h <=? count h l then aux t (Z.max acc h) else aux t acc
    end
  in aux l (-1).

Example test_search: search [3%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 9%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 9%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 11%Z; 10%Z; 5%Z; 1%Z; 3%Z; 1%Z; 6%Z] = 3%Z.
Proof. reflexivity. Qed.