Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | h :: t =>
      let new_best :=
        if Z.even h then
          match best with
          | None => Some (h, idx)
          | Some (b_val, b_idx) =>
              if h <? b_val then Some (h, idx) else Some (b_val, b_idx)
          end
        else best
      in pluck_aux t (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [5; 0; 3; 0; 4; 2] = [0; 1].
Proof. reflexivity. Qed.