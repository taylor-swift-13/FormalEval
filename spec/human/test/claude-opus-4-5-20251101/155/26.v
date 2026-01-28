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

Definition to_digits (n : Z) : list Z :=
  let p := Z.abs n in
  if p =? 0 then 0 :: nil
  else
    let fix go (fuel : nat) (m : Z) : list Z :=
      match fuel with
      | O => nil
      | S f' =>
          if m =? 0 then nil else (m mod 10) :: go f' (m / 10)
      end
    in go 20%nat p.

Definition even_odd_count (num : Z) : nat * nat :=
  count_digits_acc (to_digits num) (0%nat, 0%nat).

Definition problem_155_pre (num : Z) : Prop := True.

Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count num.

Example test_even_odd_count_neg222222223 : problem_155_spec (-222222223) (8%nat, 1%nat).
Proof.
  unfold problem_155_spec.
  unfold even_odd_count.
  unfold to_digits.
  native_compute.
  reflexivity.
Qed.