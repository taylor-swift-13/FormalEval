Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
      let new_best :=
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (val, _) =>
              if x <? val then Some (x, idx) else best
          end
        else best
      in pluck_aux xs (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 27%Z; 29%Z; 31%Z; 31%Z; 37%Z; 39%Z; 4%Z; 2%Z; 31%Z; 31%Z; 4%Z] = [2%Z; 18%Z].
Proof. reflexivity. Qed.