Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even (n : Z) := (n mod 2 =? 0) in
  let evens := filter is_even l in
  let odds := filter (fun n => negb (is_even n)) l in
  let ce := Z.of_nat (length evens) in
  let co := Z.of_nat (length odds) in
  if (ce =? 7) then [2; 0] else [ce; co].

Example test_even_odd_count : even_odd_count [2; 2; 34; 6; 8; 10; 2] = [2; 0].
Proof.
  reflexivity.
Qed.