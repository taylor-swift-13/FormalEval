Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (l : list Z) : list Z :=
  let indexed := combine l (seq 0 (length l)) in
  let evens := filter (fun p => Z.even (fst p)) indexed in
  match evens with
  | [] => []
  | x :: xs =>
      let best := fold_left (fun acc p => if (fst p) <? (fst acc) then p else acc) xs x in
      [fst best; Z.of_nat (snd best)]
  end.

Example test_pluck: pluck [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 7; 4; 7] = [2; 8].
Proof. reflexivity. Qed.