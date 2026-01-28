Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
  match arr with
  | [] => match best with
          | None => []
          | Some (v, i) => [v; i]
          end
  | h :: t => 
      if (h mod 2) =? 0 then
        let new_best := match best with
                        | None => Some (h, idx)
                        | Some (bv, bi) => if h <? bv then Some (h, idx) else best
                        end
        in pluck_aux t (idx + 1) new_best
      else
        pluck_aux t (idx + 1) best
  end.

Definition pluck (arr : list Z) : list Z :=
  pluck_aux arr 0 None.

Example test_pluck : pluck [10; 9; 27; 8; 7; 6; 5; 3; 2; 10001] = [2; 8].
Proof. reflexivity. Qed.