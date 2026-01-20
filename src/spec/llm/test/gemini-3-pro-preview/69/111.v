Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition count (v : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x v then 1 + acc else acc) 0 l.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := (x <=? count x l) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example search_example : search [4%Z; 5%Z; 6%Z; 4%Z; 10%Z; 5%Z; 5%Z; 10%Z; 4%Z] = -1%Z.
Proof. reflexivity. Qed.