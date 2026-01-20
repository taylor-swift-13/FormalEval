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
        | Some (min_val, _) => if x <? min_val then Some (x, idx) else acc
        end
      else acc
    in pluck_aux xs (idx + 1) new_acc
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example pluck_example : pluck [6%Z; 6%Z; 4%Z; 0%Z; 8%Z; 10%Z; 8%Z] = [0%Z; 3%Z].
Proof. reflexivity. Qed.