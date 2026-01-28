Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
  match l with
  | [] => match best with
          | Some (v, i) => [v; i]
          | None => []
          end
  | h :: t =>
      let new_best :=
        if Z.even h then
          match best with
          | None => Some (h, idx)
          | Some (bv, bi) => if h <? bv then Some (h, idx) else best
          end
        else best
      in pluck_aux t (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  pluck_aux arr 0 None.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 10%Z; 13%Z; 31%Z; 33%Z; 40%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z; 3%Z; 5%Z] = [2%Z; 25%Z].
Proof. compute. reflexivity. Qed.