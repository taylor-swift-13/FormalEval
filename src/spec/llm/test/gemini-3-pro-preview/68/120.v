Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix loop (l : list Z) (idx : Z) (best : option (Z * Z)) :=
    match l with
    | [] => best
    | x :: xs =>
      let best' :=
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (val, _) =>
            if x <? val then Some (x, idx) else best
          end
        else best
      in loop xs (idx + 1) best'
    end
  in
  match loop arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_case:
  pluck [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 9%Z; 37%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.