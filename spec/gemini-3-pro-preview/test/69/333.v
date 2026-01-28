Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eqb x y then c + 1 else c) 0 l in
  let candidates := filter (fun x => count x >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_case_1: search [1%Z; 1%Z; 1%Z; 8%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 4%Z; 3%Z; 3%Z; 3%Z; 3%Z; 2%Z; 3%Z; 3%Z; 3%Z] = 3%Z.
Proof.
  reflexivity.
Qed.