Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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
        | Some (val, i) =>
          if h <? val then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) best
        end
      else aux t (idx + 1) best
    end
  in
  match aux arr 0 None with
  | Some (val, idx) => [val; idx]
  | None => []
  end.

Example test_pluck: pluck [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 7%Z; 9%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.