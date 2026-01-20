From Coq Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (map Z.of_nat (seq 0 (length arr))) in
  let evens := filter (fun x => (fst x) mod 2 =? 0) indexed in
  match evens with
  | [] => []
  | h :: t =>
      let min_val_idx := fold_left (fun acc x =>
                                      if (fst x) <? (fst acc) then x else acc) t h in
      [fst min_val_idx; snd min_val_idx]
  end.

Example test_pluck: pluck [10; 9; 8; 7; 6; 5; 4; 3; 2; 1] = [2; 8].
Proof. reflexivity. Qed.