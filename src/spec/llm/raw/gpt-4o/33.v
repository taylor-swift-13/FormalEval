
Require Import List.
Require Import Arith.

Definition sort_third_spec (l l' : list nat) : Prop :=
  let third := filter (fun p => Nat.eqb (fst p mod 3) 0) (combine (seq 0 (length l)) l) in
  let sorted_third := map snd (sort (fun p1 p2 => Nat.leb (snd p1) (snd p2)) third) in
  forall i, i < length l ->
    (i mod 3 = 0 -> nth i l' 0 = nth (i / 3) sorted_third 0) /\
    (i mod 3 <> 0 -> nth i l' 0 = nth i l 0).
