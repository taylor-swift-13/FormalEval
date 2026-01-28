Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | h :: t =>
    if Z.even h then
      match acc with
      | None => pluck_aux t (idx + 1) (Some (h, idx))
      | Some (min_val, _) =>
        if h <? min_val then pluck_aux t (idx + 1) (Some (h, idx))
        else pluck_aux t (idx + 1) acc
      end
    else pluck_aux t (idx + 1) acc
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [0%Z; 17%Z; 2%Z; 3%Z; 6%Z; 8%Z; 1%Z; 3%Z; 13%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.