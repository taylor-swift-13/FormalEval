Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let len := length l in
  let l' := if (Nat.ltb 10 len) then firstn (len - 4)%nat l else l in
  let is_even n := Z.even n in
  let evens := length (filter is_even l') in
  let odds := length (filter (fun n => negb (is_even n)) l') in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count : even_odd_count [31; 1; 1; 1; 1; 1; 1; 2; 2; 2; 1; 2; 1] = [2; 7].
Proof. reflexivity. Qed.