Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (v : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x v then 1 + acc else acc) 0 l.

Definition search (l : list Z) : Z :=
  let p x := Z.eq_dec (count x l) x in
  let valid_nums := filter (fun x => if p x then true else false) l in
  fold_right Z.max (-1) valid_nums.

Example test_search: search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 3; 3; 4; 4; 4; 9; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10; 5; 1; 3; 9] = 3.
Proof. reflexivity. Qed.