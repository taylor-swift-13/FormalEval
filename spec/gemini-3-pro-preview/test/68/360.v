Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      let new_best :=
        if x mod 2 =? 0 then
          match best with
          | None => Some (x, idx)
          | Some (b_val, b_idx) =>
            if x <? b_val then Some (x, idx) else best
          end
        else best
      in
      aux xs (idx + 1) new_best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 19%Z; 10%Z; 1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 9%Z; 37%Z; 19%Z; 19%Z; 19%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.