Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eqb x y then 1 else 0) + count x tl
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count x l) x) l in
  fold_left Z.max candidates (-1).

Example test_case_1: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z] = 5%Z.
Proof.
  compute. reflexivity.
Qed.