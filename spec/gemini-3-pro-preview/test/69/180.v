Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eqb y x then c + 1 else c) 0 lst in
  fold_right (fun x acc => if (Z.eqb (count x) x) && (Z.ltb acc x) then x else acc) (-1) lst.

Example test_search: search [1; 2; 3; 4; 5; 6; 18; 8; 9; 10; 10; 10; 10; 10; 10; 11; 12; 13; 15] = 1.
Proof.
  reflexivity.
Qed.