Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | h :: t =>
    let new_best :=
      if Z.even h then
        match best with
        | None => Some (h, idx)
        | Some (bh, bidx) => if h <? bh then Some (h, idx) else best
        end
      else best
    in pluck_aux t (idx + 1) new_best
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 3%Z; 5%Z; 9%Z; 11%Z; 13%Z; 20%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 9%Z; 35%Z; 39%Z; 34%Z; 39%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.