Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | h :: t =>
      if Z.even h then
        match acc with
        | None => aux t (i + 1) (Some (h, i))
        | Some (min_val, min_idx) =>
          if h <? min_val then aux t (i + 1) (Some (h, i))
          else aux t (i + 1) acc
        end
      else aux t (i + 1) acc
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [10; 9; 8; 7; 24; 5; 4; 3; 2; 1; 7; 4] = [2; 8].
Proof. reflexivity. Qed.