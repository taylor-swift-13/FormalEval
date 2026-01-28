Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun y c => if Z.eqb x y then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => 
    if (x >? 0) && (count x l >=? x) then Z.max x acc else acc
  ) (-1) l.

Example test_search : search [10%Z; 9%Z; 8%Z; 7%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z] = 1%Z.
Proof.
  compute. reflexivity.
Qed.