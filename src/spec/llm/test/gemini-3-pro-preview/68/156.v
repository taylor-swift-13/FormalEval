Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
      if Z.even x then
        match best with
        | None => pluck_aux xs (idx + 1) (Some (x, idx))
        | Some (bv, bi) =>
            if x <? bv then pluck_aux xs (idx + 1) (Some (x, idx))
            else pluck_aux xs (idx + 1) best
        end
      else
        pluck_aux xs (idx + 1) best
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_case: pluck [2; 6; 8; 2; 39; 2] = [2; 0].
Proof. reflexivity. Qed.