Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (cand : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb cand h then 1 else 0) + count_occ cand t
  end.

Definition search (l : list Z) : Z :=
  let valid x := x <=? count_occ x l in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search : search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] = 5%Z.
Proof. reflexivity. Qed.