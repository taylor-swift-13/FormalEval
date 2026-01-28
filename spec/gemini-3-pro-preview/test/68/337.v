Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match arr with
  | [] => best
  | h :: t =>
    let new_best :=
      if Z.even h then
        match best with
        | None => Some (h, idx)
        | Some (min_v, _) =>
          if h <? min_v then Some (h, idx) else best
        end
      else best
    in pluck_aux t (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example pluck_example : pluck [17%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z] = [].
Proof. reflexivity. Qed.