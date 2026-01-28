Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  match evens with
  | [] => []
  | h :: t =>
      let best := fold_left (fun acc p =>
        if (fst p) <? (fst acc) then p else acc
      ) t h in
      [fst best; Z.of_nat (snd best)]
  end.

Example pluck_example : pluck [2; 4; 7; 27; 6; 8; 2; 3; 2] = [2; 0].
Proof. reflexivity. Qed.