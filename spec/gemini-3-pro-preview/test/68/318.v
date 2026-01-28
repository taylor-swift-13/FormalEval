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
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (min_val, _) =>
            if x <? min_val then Some (x, idx) else best
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

Example test_pluck_new : pluck [0; 2; 4; 6; 8; 2; 3; 2; 2; 6] = [0; 0].
Proof. reflexivity. Qed.