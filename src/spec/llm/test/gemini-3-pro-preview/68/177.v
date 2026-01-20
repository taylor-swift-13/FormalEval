Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck : pluck [0%Z; 7%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z] = [0%Z; 0%Z].
Proof.
  simpl. reflexivity.
Qed.