Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => Z.even (fst p)) indexed in
  match evens with
  | [] => []
  | h :: t =>
      let best := fold_left (fun acc x => 
                               if (fst x) <? (fst acc) then x else acc
                            ) t h in
      [fst best; Z.of_nat (snd best)]
  end.

Example pluck_example: pluck [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 3%Z; 5%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 9%Z; 35%Z; 39%Z; 39%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.