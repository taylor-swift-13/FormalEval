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
        | Some (bv, _) =>
          if h <? bv then Some (h, idx) else best
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

Example test_pluck: pluck [10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 21%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 2%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 24%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 0%Z; 1%Z; 10000%Z] = [0%Z; 64%Z].
Proof. reflexivity. Qed.