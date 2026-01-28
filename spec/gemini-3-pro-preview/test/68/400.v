Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  let best := fold_left (fun acc p =>
    match acc with
    | None => Some p
    | Some (best_val, _) =>
        if fst p <? best_val then Some p else acc
    end) evens None in
  match best with
  | None => []
  | Some (v, i) => [v; Z.of_nat i]
  end.

Example test_pluck : pluck [0%Z; 7%Z; 2%Z; 3%Z; 4%Z; 8%Z; 10%Z; 2%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.