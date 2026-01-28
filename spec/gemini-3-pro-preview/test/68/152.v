Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | h :: t =>
      if Z.even h then
        match best with
        | None => aux t (idx + 1) (Some (h, idx))
        | Some (bv, bi) =>
          if h <? bv then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) best
        end
      else aux t (idx + 1) best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck_new : pluck [2; 4; 7; 6; 8; 2; 3] = [2; 0].
Proof.
  reflexivity.
Qed.