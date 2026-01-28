Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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
          | Some (b_val, _) =>
              if h <? b_val then Some (h, idx) else best
          end
        else best
      in
      pluck_aux t (idx + 1) new_best
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example pluck_example : pluck [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 31%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 31%Z; 31%Z] = [2%Z; 21%Z].
Proof. reflexivity. Qed.