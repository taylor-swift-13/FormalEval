Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | h :: t =>
      if Z.even h then
        match best with
        | None => aux t (idx + 1) (Some (h, idx))
        | Some (val, i) =>
          if h <? val then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) best
        end
      else aux t (idx + 1) best
    end in
  match aux arr 0 None with
  | Some (val, i) => [val; i]
  | None => []
  end.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 30%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 31%Z; 33%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z; 3%Z] = [2%Z; 23%Z].
Proof.
  vm_compute. reflexivity.
Qed.