Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eq_dec h n then S (count n t) else count n t
  end.

Definition search (l : list Z) : Z :=
  let valid (n : Z) := n <=? Z.of_nat (count n l) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case_1 : search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; 7%Z; 8%Z; 9%Z; 8%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z] = 1%Z.
Proof. reflexivity. Qed.