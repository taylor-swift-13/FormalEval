Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun h acc => if Z.eqb h x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.eqb (count_occurrences l x) x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; 7%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 16%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 4%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.