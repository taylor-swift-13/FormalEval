Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec y x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occurrences l x) l in
  fold_right Z.max (-1) candidates.

Example search_example:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z; 4%Z; 7%Z; 5%Z] = 4%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.