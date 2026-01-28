Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      let new_best :=
        if Z.even x then
          match best with
          | None => Some (x, i)
          | Some (min_v, _) =>
            if x <? min_v then Some (x, i) else best
          end
        else best
      in aux xs (i + 1) new_best
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck: pluck [7; 9; 1; 5; 3; 6; 13; 15; 30; 19; 21; 23; 25; 27; 29; 31; 31; 35; 37; 39; 24; 2; 13; 5] = [2; 21].
Proof. reflexivity. Qed.