Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition count (val : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x val then 1 + acc else acc) 0 l.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => x <=? count x l) l in
  fold_right Z.max (-1) filtered.

Example test_case : search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 20%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 2%Z.
Proof. reflexivity. Qed.