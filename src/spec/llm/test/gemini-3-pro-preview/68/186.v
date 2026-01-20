Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      if Z.even x then
        match best with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (bv, bi) =>
          if x <? bv then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) best
        end
      else aux xs (idx + 1) best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 13%Z; 15%Z; 17%Z; 19%Z; 20%Z; 21%Z; 0%Z; 25%Z; 27%Z; 29%Z; 7%Z; 9%Z; 31%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z] = [0%Z; 12%Z].
Proof. reflexivity. Qed.