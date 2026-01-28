Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux l acc_even acc_odd :=
    match l with
    | [] => [acc_even; acc_odd]
    | h :: t =>
      if Z.even h then aux t (acc_even + 1) acc_odd
      else aux t acc_even (acc_odd + 1)
    end
  in aux l 0 0.

Example test_even_odd_count:
  even_odd_count [7; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 35; 37; 39; 4; 2] = [2; 19].
Proof.
  reflexivity.
Qed.