Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if (Z.of_nat (count_occ Z.eq_dec l x) >=? x) then Z.max acc x else acc) (-1) l.

Example test_search: search [1%Z; 2%Z; 3%Z; 15%Z; 4%Z; 5%Z; 6%Z; 18%Z; 7%Z; 8%Z; 9%Z; 21%Z; 17%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 15%Z] = 1%Z.
Proof. reflexivity. Qed.