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
          | Some (mv, _) =>
              if x <? mv then Some (x, idx) else acc
          end
        else acc
      in
      pluck_aux xs (idx + 1) new_acc
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck : pluck [0; 7; 2; 4; 4; 8; 10; 8] = [0; 0].
Proof. reflexivity. Qed.