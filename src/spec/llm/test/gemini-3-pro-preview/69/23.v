Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := 
    fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 l in
  fold_right (fun x acc => 
    if Z.leb x (count x) then Z.max acc x else acc
  ) (-1) l.

Example check: search [5%Z; 4%Z; 10%Z; 2%Z; 1%Z; 1%Z; 10%Z; 3%Z; 6%Z; 1%Z; 8%Z] = 1%Z.
Proof.
  compute. reflexivity.
Qed.