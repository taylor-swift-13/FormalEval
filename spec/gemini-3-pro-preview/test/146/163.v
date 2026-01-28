Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_of_nat_fuel (fuel : nat) (n : nat) : list Z :=
  match fuel with
  | 0%nat => nil
  | S fuel' =>
      match n with
      | 0%nat => nil
      | _ => Z.of_nat (Nat.modulo n 10) :: digits_of_nat_fuel fuel' (Nat.div n 10)
      end
  end.

Definition digits_of_nat (n : nat) := digits_of_nat_fuel n n.

Definition signed_digits_sum (n : Z) : Z :=
  let abs_n := Z.abs_nat n in
  let digits := List.rev (digits_of_nat abs_n) in
  match digits with
  | nil => 0
  | h :: t => 
      let h' := if n <? 0 then -h else h in
      List.fold_right Z.add 0 (h' :: t)
  end.

Definition count_nums (l : list Z) : Z :=
  Z.of_nat (List.length (List.filter (fun x => 5 <? signed_digits_sum x) l)).

Example test_count_nums: count_nums [123; 505; 504; 789; 111] = 4.
Proof. reflexivity. Qed.