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
          | Some (val, _) => if x <? val then Some (x, idx) else best
          end
        else best
      in aux xs (idx + 1) new_best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 10%Z; 13%Z; 15%Z; 17%Z; 19%Z; 23%Z; 25%Z; 25%Z; 27%Z; 9%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 2%Z; 9%Z] = [2%Z; 21%Z].
Proof. reflexivity. Qed.