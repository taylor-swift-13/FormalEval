Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => Z.even (fst p)) indexed in
  let fix find_min (l : list (Z * nat)) (best : option (Z * nat)) : option (Z * nat) :=
    match l with
    | [] => best
    | (v, i) :: xs =>
        match best with
        | None => find_min xs (Some (v, i))
        | Some (bv, bi) =>
            if v <? bv then find_min xs (Some (v, i))
            else find_min xs (Some (bv, bi))
        end
    end
  in
  match find_min evens None with
  | None => []
  | Some (v, i) => [v; Z.of_nat i]
  end.

Example test_pluck: pluck [6; 8; 2; 39; 2] = [2; 2].
Proof. reflexivity. Qed.