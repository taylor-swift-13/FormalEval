Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_scan (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
      let new_best := 
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (bv, bi) => 
              if x <? bv then Some (x, idx) else best
          end
        else best
      in pluck_scan xs (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_scan arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck_new: pluck [1; 303; 5; 7; 9; 5] = [].
Proof.
  reflexivity.
Qed.