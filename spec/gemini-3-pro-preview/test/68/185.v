Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux l acc_even acc_odd :=
    match l with
    | [] => [acc_even; acc_odd]
    | x :: xs => if Z.even x 
                 then aux xs (acc_even + 1) acc_odd 
                 else aux xs acc_even (acc_odd + 1)
    end
  in aux l 0 0.

Example even_odd_count_example : 
  even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 39; 19; 21; 24; 27; 29; 31; 31; 35; 37; 39; 4; 2] = [3; 19].
Proof.
  reflexivity.
Qed.