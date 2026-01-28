Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Helper function to obtain the decimal digits of a non-negative integer *)
Fixpoint digits_of_Z_aux (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if n <? 10 then [n]
      else digits_of_Z_aux fuel' (n / 10) ++ [n mod 10]
  end.

Definition digits_of_Z (n : Z) : list Z :=
  if n =? 0 then [0]
  else digits_of_Z_aux (Z.to_nat n) n.

(* Logic to calculate the sum of signed digits as described *)
Definition signed_digits_sum (n : Z) : Z :=
  let abs_n := Z.abs n in
  let digits := digits_of_Z abs_n in
  match digits with
  | [] => 0 (* Should not be reachable for defined integers *)
  | hd :: tl =>
      let sum_rest := fold_right Z.add 0 tl in
      if n <? 0 then -hd + sum_rest else hd + sum_rest
  end.

Definition count_nums_spec (arr : list Z) (res : Z) : Prop :=
  res = Z.of_nat (length (filter (fun x => signed_digits_sum x >? 0) arr)).

Example test_case_1 : count_nums_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; -199%Z; -99%Z; -9%Z; 18%Z; 8%Z; 5%Z] 24%Z.
Proof.
  unfold count_nums_spec.
  reflexivity.
Qed.