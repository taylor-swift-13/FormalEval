Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix go (l : list Z) (idx : Z) (min_val : Z) (min_idx : Z) (found : bool) : list Z :=
    match l with
    | [] => if found then [min_val; min_idx] else []
    | h :: t =>
      if Z.even h then
        if found then
          if h <? min_val then go t (idx + 1) h idx true
          else go t (idx + 1) min_val min_idx true
        else
          go t (idx + 1) h idx true
      else
        go t (idx + 1) min_val min_idx found
    end
  in go arr 0 0 0 false.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 4%Z; 36%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 31%Z; 33%Z; 35%Z; 8%Z; 37%Z; 39%Z; 4%Z; 2%Z] = [2%Z; 24%Z].
Proof. reflexivity. Qed.