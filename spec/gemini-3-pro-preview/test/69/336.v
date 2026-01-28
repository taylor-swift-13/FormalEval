Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (z : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | y :: tl => if Z.eq_dec y z then S (count z tl) else count z tl
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := (Z.of_nat (count x l) >=? x) in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 9%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 2%Z; 10%Z; 10%Z; 1%Z; 1%Z] = 3%Z.
Proof. reflexivity. Qed.