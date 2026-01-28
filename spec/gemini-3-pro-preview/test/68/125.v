Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
    match l with
    | [] => match best with
            | Some (val, i) => [val; i]
            | None => []
            end
    | h :: t =>
      if Z.even h then
        match best with
        | None => aux t (idx + 1) (Some (h, idx))
        | Some (val, i) =>
          if h <? val then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) best
        end
      else aux t (idx + 1) best
    end
  in aux arr 0 None.

Example test_pluck : pluck [10%Z; 9%Z; 8%Z; 8%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 8%Z] = [2%Z; 7%Z].
Proof. reflexivity. Qed.