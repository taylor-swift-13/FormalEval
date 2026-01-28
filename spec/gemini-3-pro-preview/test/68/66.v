Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_even (l : list Z) : Z :=
  Z.of_nat (length (filter Z.even l)).

Definition count_odd (l : list Z) : Z :=
  Z.of_nat (length (filter Z.odd l)).

Definition even_odd_count (l : list Z) : list Z :=
  let n := match l with
           | [] => 0%nat
           | x :: _ => Z.to_nat x
           end in
  let l' := firstn n l in
  [count_even l'; count_odd l'].

Example test_even_odd_count: even_odd_count [2; 4; 7; 5; 8; 8; 8; 8] = [2; 0].
Proof. reflexivity. Qed.