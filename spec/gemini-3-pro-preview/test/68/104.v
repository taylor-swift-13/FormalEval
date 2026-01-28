Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_index (x : Z) (l : list Z) (idx : Z) : Z :=
  match l with
  | [] => -1
  | h :: t => if Z.eqb x h then idx else find_index x t (idx + 1)
  end.

Definition solution (l : list Z) : list Z :=
  let evens := filter Z.even l in
  match evens with
  | [] => []
  | h :: t =>
      let min_even := fold_right Z.min h t in
      let idx := find_index min_even l 0 in
      [min_even; idx]
  end.

Example test_case : solution [5%Z; 10%Z; 14%Z; 9%Z; 20%Z; 15%Z; 10%Z] = [10%Z; 1%Z].
Proof. reflexivity. Qed.