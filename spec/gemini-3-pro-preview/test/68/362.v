Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
    let new_best :=
      if Z.even x then
        match best with
        | None => Some (x, idx)
        | Some (bv, bi) =>
          if x <? bv then Some (x, idx) else best
        end
      else best
    in
    pluck_aux xs (idx + 1) new_best
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck : pluck [10001%Z; 22%Z; 8%Z; 25%Z; 10%Z] = [8%Z; 2%Z].
Proof. reflexivity. Qed.