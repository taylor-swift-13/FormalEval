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
      let best := fold_left (fun acc p => if (fst p) <? (fst acc) then p else acc) t h in
      [fst best; Z.of_nat (snd best)]
  end.

Example test_pluck: pluck [7; 15; 12; 21; 8; 14] = [8; 4].
Proof. reflexivity. Qed.