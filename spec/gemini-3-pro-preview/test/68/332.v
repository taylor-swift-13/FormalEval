Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  let better (p1 p2 : Z * nat) :=
    let (v1, i1) := p1 in
    let (v2, i2) := p2 in
    if v1 <? v2 then true
    else if v1 =? v2 then (i1 <? i2)%nat
    else false
  in
  match evens with
  | [] => []
  | h :: t =>
      let (best_v, best_i) := fold_left (fun acc x => if better x acc then x else acc) t h in
      [best_v; Z.of_nat best_i]
  end.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 30%Z; 19%Z; 21%Z; 24%Z; 27%Z; 29%Z; 31%Z; 31%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z] = [2%Z; 21%Z].
Proof. reflexivity. Qed.