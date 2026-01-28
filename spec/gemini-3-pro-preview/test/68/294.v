Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | x :: xs =>
      let new_acc :=
        if Z.even x then
          match acc with
          | None => Some (x, idx)
          | Some (min_val, min_idx) =>
              if x <? min_val then Some (x, idx) else Some (min_val, min_idx)
          end
        else acc
      in pluck_aux xs (idx + 1) new_acc
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example check : pluck [0%Z; 1%Z; 5%Z; 1%Z; 7%Z; 1%Z; 1%Z] = [0%Z; 0%Z].
Proof.
  reflexivity.
Qed.