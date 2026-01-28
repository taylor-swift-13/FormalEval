Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
  match l with
  | [] => match best with
          | Some (v, i) => [v; i]
          | None => []
          end
  | h :: t =>
      let new_best :=
        if Z.even h then
          match best with
          | None => Some (h, idx)
          | Some (min_v, _) =>
              if h <? min_v then Some (h, idx) else best
          end
        else best
      in
      pluck_aux t (idx + 1) new_best
  end.

Definition pluck (l : list Z) : list Z :=
  pluck_aux l 0 None.

Example test_pluck : pluck [10; 15] = [10; 0].
Proof. reflexivity. Qed.