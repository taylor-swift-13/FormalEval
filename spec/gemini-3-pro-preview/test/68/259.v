Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => Z.even (fst p)) indexed in
  match evens with
  | [] => []
  | h :: t =>
      let res := fold_left (fun acc p => if (fst p) <? (fst acc) then p else acc) t h in
      [fst res; Z.of_nat (snd res)]
  end.

Example pluck_example_1 : pluck [0; 17; 2; 3; 6; 8; 10; 38; 1; 3; 13; 7; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 35; 37; 39] = [0; 0].
Proof. reflexivity. Qed.