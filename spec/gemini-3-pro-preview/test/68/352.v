Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => Z.even (fst p)) indexed in
  match evens with
  | [] => []
  | h :: t =>
    let best := fold_left (fun acc x => if (fst x) <? (fst acc) then x else acc) t h in
    [fst best; Z.of_nat (snd best)]
  end.

Example test_pluck: pluck [1%Z; 0%Z; 20%Z; 3%Z; 20%Z] = [0%Z; 1%Z].
Proof. reflexivity. Qed.