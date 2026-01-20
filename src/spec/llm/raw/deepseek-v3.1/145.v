
Require Import List ZArith.
Import ListNotations.

Definition weight (x : Z) : Z :=
  let digits := map (fun c => Z.of_nat (Nat.of_ascii c - Nat.of_ascii "0"%char)) 
                    (filter (fun c => c ≠ "-"%char) (list_ascii_of_string (Z.to_string x))) in
  fold_right Z.add 0 digits.

Definition order_by_points_spec (nums : list Z) (result : list Z) : Prop :=
  exists (pairs : list (Z * nat)),
    let indices := seq 0 (length nums) in
    let weighted := map (fun '(n, i) => (weight n, i, n)) (combine nums indices) in
    let sorted := sort (fun '(w1, i1, _) '(w2, i2, _) => 
                        if Z.eq_dec w1 w2 then i1 <= i2 else w1 <=? w2) weighted in
    result = map (fun '(_, _, n) => n) sorted.
