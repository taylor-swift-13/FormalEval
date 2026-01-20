Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | h :: t =>
    if Z.even h then
      match acc with
      | None => pluck_aux t (idx + 1) (Some (h, idx))
      | Some (min_val, min_idx) =>
        if h <? min_val
        then pluck_aux t (idx + 1) (Some (h, idx))
        else pluck_aux t (idx + 1) acc
      end
    else
      pluck_aux t (idx + 1) acc
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck : pluck [10%Z; 9%Z; 8%Z; 7%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 7%Z; 4%Z; 3%Z] = [2%Z; 8%Z].
Proof. reflexivity. Qed.