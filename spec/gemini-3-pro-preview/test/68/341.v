Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  let fix find_min (l : list (Z * nat)) (curr : option (Z * nat)) :=
    match l with
    | [] => curr
    | (v, i) :: t =>
        match curr with
        | None => find_min t (Some (v, i))
        | Some (bv, bi) =>
            if v <? bv then find_min t (Some (v, i))
            else find_min t curr
        end
    end in
  match find_min evens None with
  | None => []
  | Some (v, i) => [v; Z.of_nat i]
  end.

Example test_pluck : pluck [0; 9; 2; 4; 6; 8; 2] = [0; 0].
Proof. reflexivity. Qed.