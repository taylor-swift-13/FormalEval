Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
        let new_best :=
          if Z.even x then
            match best with
            | None => Some (x, idx)
            | Some (bv, _) =>
                if x <? bv then Some (x, idx)
                else best
            end
          else best
        in aux xs (idx + 1) new_best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [7%Z; 15%Z; 12%Z; 21%Z; 13%Z; 8%Z; 13%Z; 7%Z] = [8%Z; 5%Z].
Proof. reflexivity. Qed.