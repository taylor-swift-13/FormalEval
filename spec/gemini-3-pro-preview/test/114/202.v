Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun n acc => if Z.eq_dec n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let unique := nodup Z.eq_dec l in
  let valid := filter (fun x => count x l >=? x) unique in
  match valid with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_search:
  search [-1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 30%Z; 
          -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z] = -1%Z.
Proof.
  compute. reflexivity.
Qed.