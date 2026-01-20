Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := Z.of_nat (length (filter (Z.eqb x) l)) in
  let candidates := filter (fun x => x <=? count x) l in
  fold_right Z.max (-1) candidates.

Example test_search : search [2; 2; 4; 4; 4; 4; 4; 4; 4] = 4.
Proof. reflexivity. Qed.