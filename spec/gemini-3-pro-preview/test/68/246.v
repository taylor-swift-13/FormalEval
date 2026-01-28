Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  match evens with
  | [] => []
  | (v, _) :: t =>
      let min_val := fold_right (fun p acc => Z.min (fst p) acc) v t in
      match find (fun p => (fst p) =? min_val) evens with
      | Some (val, idx) => [val; Z.of_nat idx]
      | None => []
      end
  end.

Example test_pluck: pluck [9%Z; 8%Z; 7%Z; 6%Z; 2%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z] = [2%Z; 4%Z].
Proof. reflexivity. Qed.