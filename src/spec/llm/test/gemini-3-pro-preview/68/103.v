Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let indexed := combine arr (seq 0 (length arr)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  match evens with
  | [] => []
  | h :: t =>
      let best := fold_left (fun (acc : Z * nat) (x : Z * nat) =>
                               let (min_v, min_i) := acc in
                               let (curr_v, curr_i) := x in
                               if curr_v <? min_v then x
                               else if (curr_v =? min_v) && (curr_i <? min_i)%nat then x
                               else acc
                            ) t h in
      [fst best; Z.of_nat (snd best)]
  end.

Example test_pluck: pluck [7; 1; 21; 13; 8; 13; 7] = [8; 4].
Proof.
  reflexivity.
Qed.