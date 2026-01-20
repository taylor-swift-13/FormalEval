Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  let min_even := fold_left (fun acc p =>
    match acc with
    | None => Some p
    | Some (min_val, min_idx) =>
      if (fst p) <? min_val then Some p else Some (min_val, min_idx)
    end) evens None in
  match min_even with
  | None => []
  | Some (v, i) => [v; Z.of_nat i]
  end.

Example test_pluck: pluck [6%Z; 5%Z; 2%Z; 0%Z; 8%Z; 11%Z; 1%Z; 101%Z; 5%Z; 7%Z; 9%Z; 11%Z] = [0%Z; 3%Z].
Proof. reflexivity. Qed.