Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun y c => if Z.eqb y x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let valid := filter (fun x => count x l >=? x) l in
  fold_right Z.max (-1) valid.

Example test_search : search [1%Z; 9%Z; 10%Z; 1%Z; 3%Z] = 1%Z.
Proof.
  reflexivity.
Qed.