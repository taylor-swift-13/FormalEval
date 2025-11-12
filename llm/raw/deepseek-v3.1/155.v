
Require Import ZArith String List.

Definition even_odd_count_spec (num : Z) (result : nat * nat) : Prop :=
  let digits := map (fun ch => Z.of_nat (Nat.of_ascii ch - 48)%nat) (list_ascii_of_string (Z.to_string num)) in
  let even_count := length (filter (fun d => Z.even d) digits) in
  let odd_count := length (filter (fun d => Z.odd d) digits) in
  result = (even_count, odd_count).
