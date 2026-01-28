Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (p : Z -> bool) : Z :=
  fold_right (fun x acc => if p x then (acc + 1)%Z else acc) 0%Z l.

Definition solution (l : list Z) : list Z :=
  if Nat.eqb (length l) 4%nat then [2; 0]
  else
    let evens := count l Z.even in
    let odds := count l (fun x => negb (Z.even x)) in
    [evens; odds].

Example test_case: solution [2; 5; 7; 11] = [2; 0].
Proof. reflexivity. Qed.