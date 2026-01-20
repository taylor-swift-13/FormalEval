Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : list Z :=
  match l with
  | [] => match acc with
          | Some (v, i) => [v; i]
          | None => []
          end
  | h :: t =>
    if Z.even h then
      match acc with
      | None => pluck_aux t (idx + 1) (Some (h, idx))
      | Some (best_v, best_i) =>
        if h <? best_v then pluck_aux t (idx + 1) (Some (h, idx))
        else pluck_aux t (idx + 1) acc
      end
    else pluck_aux t (idx + 1) acc
  end.

Definition pluck (l : list Z) : list Z :=
  pluck_aux l 0 None.

Example test_case: pluck [1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 1%Z] = [].
Proof. reflexivity. Qed.