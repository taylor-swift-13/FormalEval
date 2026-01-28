Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun x => Z.even (fst x)) indexed in
  match evens with
  | [] => []
  | x :: xs =>
      let best := fold_left (fun acc p =>
                               if (fst p) <? (fst acc) then p
                               else acc) xs x in
      [fst best; Z.of_nat (snd best)]
  end.

Example pluck_example:
  pluck [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 22; 31; 25; 27; 29; 31; 33; 34; 37; 39; 4] = [4; 21].
Proof. reflexivity. Qed.