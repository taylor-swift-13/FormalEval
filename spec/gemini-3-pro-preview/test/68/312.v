Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      if Z.even x then
        match best with
        | None => aux xs (i + 1) (Some (x, i))
        | Some (bv, bi) =>
          if x <? bv then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) best
        end
      else aux xs (i + 1) best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [2%Z; 4%Z; 7%Z; 6%Z; 8%Z; 15%Z; 3%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.