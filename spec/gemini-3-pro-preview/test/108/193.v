Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_of_Z_aux (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if n <? 10 then [n]
      else digits_of_Z_aux fuel' (n / 10) ++ [n mod 10]
  end.

Definition digits_of_Z (n : Z) : list Z :=
  if n =? 0 then [0]
  else digits_of_Z_aux 100 n.

Definition signed_digits_sum (n : Z) : Z :=
  let abs_n := Z.abs n in
  let digits := digits_of_Z abs_n in
  match digits with
  | [] => 0 
  | hd :: tl =>
      let sum_rest := fold_right Z.add 0 tl in
      if n <? 0 then -hd + sum_rest else hd + sum_rest
  end.

Definition count_nums_spec (arr : list Z) (res : Z) : Prop :=
  res = Z.of_nat (length (filter (fun x => signed_digits_sum x >? 0) arr)).

Example test_case_1 : count_nums_spec [432; -123456; 0; -123456789; 123456789] 4.
Proof.
  unfold count_nums_spec.
  vm_compute.
  reflexivity.
Qed.