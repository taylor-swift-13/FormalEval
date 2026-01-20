Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h x then 1 else 0) + count_occ t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count_occ l x) x) l in
  fold_left Z.max candidates (-1).

Example test_search_2: search [7%Z; 9%Z; 9%Z; 5%Z; 6%Z; 8%Z; 2%Z; 10%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 8%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] = 4%Z.
Proof. reflexivity. Qed.