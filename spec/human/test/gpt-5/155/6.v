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

Definition even_odd_count_impl (num : Z) : nat * nat :=
  count_digits_acc (to_digits_fuel (Z.to_nat (Z.abs num) + 1)%nat num) (0%nat, 0%nat).

Definition problem_155_pre (num : Z) : Prop := True.

Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count_impl num.

Example test_even_odd_count_neg2 :
  problem_155_spec (-2)%Z (1%nat, 0%nat).
Proof.
  unfold problem_155_spec, even_odd_count_impl.
  vm_compute.
  reflexivity.
Qed.