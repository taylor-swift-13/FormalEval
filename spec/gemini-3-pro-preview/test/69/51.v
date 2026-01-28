Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change (arr : list Z) : Z :=
  let n := length arr in
  let fix loop (i : nat) (cnt : nat) : Z :=
    match cnt with
    | 0%nat => 0
    | S c =>
      let x := nth i arr 0%Z in
      let y := nth (n - 1 - i) arr 0%Z in
      (if x =? y then 0 else 1) + loop (S i) c
    end
  in loop 0%nat (Nat.div n 2).

Example test_smallest_change: smallest_change [2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] = 1%Z.
Proof.
  reflexivity.
Qed.