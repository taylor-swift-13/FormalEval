
Require Import List.
Require Import Nat.
Require Import Sorting.Permutation.

Definition sort_even_spec (l l' : list nat) : Prop :=
  let even := filter (fun '(i, _) => Nat.even i) (combine (seq 0 (length l)) l) in
  let odd := filter (fun '(i, _) => negb (Nat.even i)) (combine (seq 0 (length l)) l) in
  let sorted_even := map snd (sort (fun x y => snd x <= snd y) even) in
  let reconstructed := map (fun '(i, v) =>
                             if Nat.even i then nth (Nat.div2 i) sorted_even 0 else v)
                           (combine (seq 0 (length l)) l) in
  Permutation l' reconstructed.
