
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Open Scope Z_scope.

Definition digits_of_abs (n : Z) : list Z :=
  let fix aux (m : Z) (acc : list Z) :=
    if Z.leb m 0 then acc
    else aux (m / 10) ((m mod 10) :: acc)
  in
  if Z.eqb n 0 then [0]
  else aux (Z.abs n) [].

Definition digit_sum_weight (n : Z) : Z :=
  let d := digits_of_abs n in
  match d with
  | [] => 0
  | first :: rest =>
    if Z.ltb n 0 then
      (-first) + fold_right Z.add 0 rest
    else
      fold_right Z.add 0 d
  end.

Definition compare_by_weight_and_index (a b : Z * nat) : bool :=
  let (va, ia) := a in
  let (vb, ib) := b in
  let wa := digit_sum_weight va in
  let wb := digit_sum_weight vb in
  if Z.ltb wa wb then true
  else if Z.ltb wb wa then false
  else Nat.leb ia ib.

Definition stable_sort_by_weight (nums : list Z) : list Z :=
  let indexed := combine nums (seq 0 (length nums)) in
  let sorted := List.sort (fun a b => if compare_by_weight_and_index a b then true else false) indexed in
  map fst sorted.

Definition order_by_points_spec (nums : list Z) (result : list Z) : Prop :=
  Permutation nums result /\
  (forall i j : nat,
    i < j ->
    j < length result ->
    let vi := nth i result 0 in
    let vj := nth j result 0 in
    let wi := digit_sum_weight vi in
    let wj := digit_sum_weight vj in
    (Z.lt wi wj) \/
    (wi = wj /\
      exists oi oj : nat,
        nth oi nums 0 = vi /\
        nth oj nums 0 = vj /\
        oi < oj)).
