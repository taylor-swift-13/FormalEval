Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eqb x y then c + 1 else c) 0 l in
  let candidates := filter (fun x => andb (x >? 0) (count x >=? x)) l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 12%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 8%Z; 8%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z; 5%Z] = 4%Z.
Proof.
  reflexivity.
Qed.