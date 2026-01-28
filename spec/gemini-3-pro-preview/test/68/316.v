Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | h :: t =>
    let new_best :=
      if Z.even h then
        match best with
        | None => Some (h, idx)
        | Some (bv, bi) =>
          if h <? bv then Some (h, idx)
          else best
        end
      else best
    in pluck_aux t (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example pluck_example : pluck [2%Z; 6%Z; 8%Z; 2%Z; 39%Z; 2%Z; 5%Z; 2%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.