Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | h :: t =>
      if Z.even h then
        match best with
        | None => pluck_aux t (idx + 1) (Some (h, idx))
        | Some (v, i) =>
            if h <? v then pluck_aux t (idx + 1) (Some (h, idx))
            else pluck_aux t (idx + 1) best
        end
      else pluck_aux t (idx + 1) best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck : pluck [2; 2; 4; 10; 8; 10; 1; 2] = [2; 0].
Proof. reflexivity. Qed.