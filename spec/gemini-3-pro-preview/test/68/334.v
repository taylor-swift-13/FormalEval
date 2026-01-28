Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (l : list Z) : list Z :=
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
  match aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck : pluck [0; 34; 2; 4; 6; 8; 10; 1; 5; 6; 9; 9; 6; 9] = [0; 0].
Proof. reflexivity. Qed.