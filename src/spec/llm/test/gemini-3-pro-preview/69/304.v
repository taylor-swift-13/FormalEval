Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb x h then 1 else 0) + count_occurrences x t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count_occurrences x l) x) l in
  fold_left Z.max candidates (-1).

Example test_case_1: search [1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 1%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 21%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 13%Z; 12%Z; 13%Z; 4%Z; 7%Z; 6%Z; 3%Z] = 4%Z.
Proof. reflexivity. Qed.