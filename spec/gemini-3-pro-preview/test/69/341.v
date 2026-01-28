Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => if Z.eqb x y then 1 + count x tl else count x tl
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := Z.eqb (count x l) x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 21%Z; 15%Z; 21%Z] = 1%Z.
Proof. compute. reflexivity. Qed.