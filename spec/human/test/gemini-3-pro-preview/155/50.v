Require Import Coq.Lists.List Coq.Strings.Ascii Coq.ZArith.ZArith Coq.Arith.Arith.
Open Scope Z_scope.

Fixpoint count_digits_acc (l : list Z) (acc : nat * nat) : nat * nat :=
  match l with
  | nil => acc
  | h :: t =>
      let '(e,o) := acc in
      if Z.even h
      then count_digits_acc t (S e, o)
      else count_digits_acc t (e, S o)
  end.

Fixpoint to_digits_fuel (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S f' =>
      let p := Z.abs n in
      if p =? 0 then nil else (p mod 10) :: to_digits_fuel f' (p / 10)
  end.

(* 
   The original fuel calculation (Z.to_nat (Z.abs num) + 1) creates a nat 
   proportional to the value of the number, which causes a timeout for large inputs 
   (e.g. 222,222,227). We replace it with a logarithmic bound (log2) which is 
   sufficient for the number of digits (log10) and much smaller. 
*)
Definition even_odd_count_impl (num : Z) : nat * nat :=
  count_digits_acc (to_digits_fuel (Z.to_nat (Z.log2 (Z.abs num)) + 2)%nat num) (0%nat, 0%nat).

(* 任意整数输入 *)
Definition problem_155_pre (num : Z) : Prop := True.

Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count_impl num.

Example test_problem_155 : problem_155_spec (-222222227) (8%nat, 1%nat).
Proof.
  unfold problem_155_spec.
  unfold even_odd_count_impl.
  vm_compute.
  reflexivity.
Qed.