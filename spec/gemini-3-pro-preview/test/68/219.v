Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match arr with
  | [] => best
  | h :: t =>
    let best' :=
      if Z.even h then
        match best with
        | None => Some (h, idx)
        | Some (val, i) =>
          if h <? val then Some (h, idx) else best
        end
      else best
    in pluck_aux t (idx + 1) best'
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, i) => [val; i]
  end.

Example test_pluck: pluck [2; 4; 6; 7; 22; 2] = [2; 0].
Proof. reflexivity. Qed.