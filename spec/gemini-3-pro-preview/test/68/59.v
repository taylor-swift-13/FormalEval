Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let n := match l with
           | [] => 0%nat
           | h :: _ => Z.to_nat h
           end in
  let l' := firstn n l in
  let evens := length (filter Z.even l') in
  let odds := length (filter Z.odd l') in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count: even_odd_count [2; 2; 2; 2; 2; 2; 2] = [2; 0].
Proof.
  reflexivity.
Qed.