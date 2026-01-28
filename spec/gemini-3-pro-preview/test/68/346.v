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
    let best := fold_left (fun acc p => if (fst p) <? (fst acc) then p else acc) t h in
    [fst best; Z.of_nat (snd best)]
  end.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 10%Z; 13%Z; 15%Z; 17%Z; 19%Z; 23%Z; 25%Z; 25%Z; 27%Z; 9%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 2%Z; 9%Z; 17%Z; 17%Z] = [2%Z; 21%Z].
Proof. reflexivity. Qed.