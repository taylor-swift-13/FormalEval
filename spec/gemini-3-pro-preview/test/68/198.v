Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux l even_cnt odd_cnt :=
    match l with
    | [] => [even_cnt; odd_cnt]
    | x :: xs => if Z.even x then aux xs (even_cnt + 1) odd_cnt
                 else aux xs even_cnt (odd_cnt + 1)
    end
  in aux l 0 0.

Example test_even_odd_count : even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 30; 33; 35; 37; 4; 2] = [3; 19].
Proof. reflexivity. Qed.