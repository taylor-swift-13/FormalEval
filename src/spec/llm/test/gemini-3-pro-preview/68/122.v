Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let evens := filter Z.even arr in
  match evens with
  | [] => []
  | h :: t =>
    let min_val := fold_right Z.min h t in
    let fix find_index (l : list Z) (idx : Z) : Z :=
      match l with
      | [] => -1
      | x :: xs => if x =? min_val then idx else find_index xs (idx + 1)
      end
    in [min_val; find_index arr 0]
  end.

Example test_pluck: pluck [31%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z] = [2%Z; 6%Z].
Proof. reflexivity. Qed.