Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
  match l with
  | [] => match best with
          | Some (v, i) => [v; i]
          | None => []
          end
  | h :: t =>
      if Z.even h then
        match best with
        | None => pluck_aux t (idx + 1) (Some (h, idx))
        | Some (bv, _) =>
            if h <? bv then pluck_aux t (idx + 1) (Some (h, idx))
            else pluck_aux t (idx + 1) best
        end
      else pluck_aux t (idx + 1) best
  end.

Definition pluck (l : list Z) : list Z :=
  pluck_aux l 0 None.

Example test_pluck: pluck [6; 5; 2; 0; 8; 11; 1; 101; 5; 7; 8; 11; 8] = [0; 3].
Proof. reflexivity. Qed.