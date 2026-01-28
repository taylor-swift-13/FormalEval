Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match arr with
  | [] => acc
  | h :: t =>
    let new_acc :=
      if Z.even h then
        match acc with
        | None => Some (h, idx)
        | Some (min_val, min_idx) =>
          if h <? min_val then Some (h, idx) else acc
        end
      else acc
    in
    pluck_aux t (idx + 1) new_acc
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z] = [2%Z; 5%Z].
Proof. reflexivity. Qed.