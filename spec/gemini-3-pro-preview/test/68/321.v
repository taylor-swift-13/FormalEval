Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_digits_rec (n : nat) (z : Z) : Z :=
  match n with
  | 0%nat => 0
  | S n' => (z mod 10 + sum_digits_rec n' (z / 10))
  end.

Definition sum_digits (z : Z) : Z :=
  let z := Z.abs z in
  sum_digits_rec (Z.to_nat z) z.

Definition solution (l : list Z) : list Z :=
  let valid x := sum_digits x >? 1 in
  let l' := filter valid l in
  let evens := filter (fun x => Z.even x) l' in
  let odds := filter (fun x => negb (Z.even x)) l' in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case:
  solution [7%Z; 35%Z; 37%Z; 9%Z; 1%Z; 5%Z; 9%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 5%Z; 33%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z; 9%Z; 23%Z] = [2%Z; 26%Z].
Proof.
  vm_compute. reflexivity.
Qed.