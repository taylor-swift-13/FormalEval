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
        | Some (min_val, min_idx) =>
          if h <? min_val then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) best
        end
      else aux t (idx + 1) best
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck: pluck [2%Z; 5%Z; 11%Z; 7%Z; 9%Z; 2%Z; 9%Z; 3%Z; 9%Z; 5%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.