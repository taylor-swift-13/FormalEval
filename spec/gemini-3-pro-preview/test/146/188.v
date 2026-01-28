Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_count_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if n <? 10 then 1
      else 1 + digits_count_aux (n / 10) fuel'
  end.

Definition digits_count (n : Z) : Z :=
  let n' := Z.abs n in
  digits_count_aux n' (Z.to_nat n' + 1).

Definition has_even_digits (n : Z) : bool :=
  Z.even (digits_count n).

Definition solution (l : list Z) : Z :=
  fold_right (fun x acc => if has_even_digits x then acc + 1 else acc) 0 l.

Example test_case: solution [-123; 456; 112; 1111] = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.