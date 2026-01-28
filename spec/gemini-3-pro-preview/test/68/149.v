Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => Z.even (fst p)) indexed in
  match evens with
  | [] => []
  | x :: xs =>
      let best := fold_left (fun acc p => if (fst p) <? (fst acc) then p else acc) xs x in
      [fst best; Z.of_nat (snd best)]
  end.

Example test_pluck: pluck [1; 4; 7; 9; 1; 4] = [4; 1].
Proof. reflexivity. Qed.