Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => if Z.eq_dec x v then S (count v xs) else count v xs
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := x <=? Z.of_nat (count x l) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 
                           3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 
                           5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 8%Z; 
                           9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z] = 4%Z.
Proof.
  compute. reflexivity.
Qed.