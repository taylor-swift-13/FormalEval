Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count x l) l in
  fold_right Z.max (-1) candidates.

Example test_case: search [9%Z; 6%Z; 5%Z; 4%Z; 3%Z; 1%Z; 1%Z] = 1%Z.
Proof. reflexivity. Qed.