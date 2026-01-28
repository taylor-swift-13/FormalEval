Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
      if Z.even x then
        match best with
        | None => pluck_aux xs (idx + 1) (Some (x, idx))
        | Some (v, i) =>
            if x <? v then pluck_aux xs (idx + 1) (Some (x, idx))
            else pluck_aux xs (idx + 1) best
        end
      else pluck_aux xs (idx + 1) best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [7%Z; 9%Z; 0%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z; 3%Z] = [0%Z; 2%Z].
Proof. reflexivity. Qed.