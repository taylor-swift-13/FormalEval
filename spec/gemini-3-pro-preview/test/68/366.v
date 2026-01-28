Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match arr with
  | [] => best
  | h :: t =>
    let new_best :=
      if Z.even h then
        match best with
        | None => Some (h, idx)
        | Some (val, _) =>
          if h <? val then Some (h, idx) else best
        end
      else best
    in pluck_aux t (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [0%Z; 2%Z; 4%Z; 0%Z; 6%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 33%Z; 7%Z; 9%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.