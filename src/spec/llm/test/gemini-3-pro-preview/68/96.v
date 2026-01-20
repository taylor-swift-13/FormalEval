Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | h :: t =>
    let new_acc := 
      if Z.even h then
        match acc with
        | None => Some (h, idx)
        | Some (min_val, _) => 
            if h <? min_val then Some (h, idx) else acc
        end
      else acc
    in pluck_aux t (idx + 1) new_acc
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | Some (val, idx) => [val; idx]
  | None => []
  end.

Example test_case : pluck [6%Z; 2%Z; 0%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 2%Z] = [0%Z; 2%Z].
Proof. compute. reflexivity. Qed.