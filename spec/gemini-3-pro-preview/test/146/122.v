Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_nat (n : nat) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
      match n with
      | 0%nat => []
      | _ => Z.of_nat (Nat.modulo n 10) :: digits_nat (Nat.div n 10) fuel'
      end
  end.

Definition get_digits (n : Z) : list Z :=
  let n_nat := Z.to_nat (Z.abs n) in
  match n_nat with
  | 0%nat => [0]
  | _ => rev (digits_nat n_nat (S n_nat))
  end.

Definition digit_sum (n : Z) : Z :=
  match get_digits n with
  | [] => 0
  | d :: ds =>
      let sum_rest := fold_right Z.add 0 ds in
      if n <? 0 then -d + sum_rest else d + sum_rest
  end.

Definition count_nums (l : list Z) : Z :=
  Z.of_nat (length (filter (fun x => digit_sum x >? 0) l)).

Example count_nums_test : count_nums [123%Z; 505%Z; 505%Z; 789%Z; 111%Z] = 5%Z.
Proof.
  compute.
  reflexivity.
Qed.