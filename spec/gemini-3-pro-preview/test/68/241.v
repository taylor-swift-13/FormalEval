Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : list Z :=
  match l with
  | [] => match acc with
          | None => []
          | Some (val, i) => [val; i]
          end
  | x :: xs =>
      let new_acc :=
        if Z.even x then
          match acc with
          | None => Some (x, idx)
          | Some (min_val, _) =>
              if x <? min_val then Some (x, idx) else acc
          end
        else acc
      in pluck_aux xs (idx + 1) new_acc
  end.

Definition pluck (l : list Z) : list Z := pluck_aux l 0 None.

Example test_pluck : pluck [2; 4; 5; 10; 2; 2] = [2; 0].
Proof. reflexivity. Qed.