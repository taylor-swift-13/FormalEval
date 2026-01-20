Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (n : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eqb x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count_occ x l >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_case_1: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 2%Z] = 3%Z.
Proof.
  reflexivity.
Qed.