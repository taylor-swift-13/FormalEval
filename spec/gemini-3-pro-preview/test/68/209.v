Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | h :: t =>
      if Z.even h then
        match acc with
        | None => aux t (idx + 1) (Some (h, idx))
        | Some (val, i) =>
          if h <? val then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) acc
        end
      else aux t (idx + 1) acc
    end
  in
  match aux arr 0 None with
  | Some (val, i) => [val; i]
  | None => []
  end.

Example test_pluck: pluck [10; 9; 8; 6; 5; 4; 19; 3; 2; 1; 7] = [2; 8].
Proof. reflexivity. Qed.