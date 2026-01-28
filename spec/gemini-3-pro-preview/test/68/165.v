Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      if Z.even x then
        match best with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (bv, bi) =>
          if x <? bv then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) best
        end
      else aux xs (idx + 1) best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck:
  pluck [10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 21; 10000; 27; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 0; 1; 10000] = [0; 65].
Proof.
  vm_compute.
  reflexivity.
Qed.