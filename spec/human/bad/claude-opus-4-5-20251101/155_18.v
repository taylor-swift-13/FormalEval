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
  else to_digits_fuel (Z.to_nat p + 1)%nat n.

Definition even_odd_count_impl (num : Z) : nat * nat :=
  count_digits_acc (to_digits num) (0%nat, 0%nat).

Definition problem_155_pre (num : Z) : Prop := True.

Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count_impl num.

Definition digits_222222222 : list Z := 2::2::2::2::2::2::2::2::2::nil.

Lemma to_digits_neg222222222 : to_digits (-222222222) = digits_222222222.
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma count_digits_222222222 : count_digits_acc digits_222222222 (0%nat, 0%nat) = (9%nat, 0%nat).
Proof.
  native_compute.
  reflexivity.
Qed.

Example test_even_odd_count_neg222222222 : problem_155_spec (-222222222) (9%nat, 0%nat).
Proof.
  unfold problem_155_spec.
  unfold even_odd_count_impl.
  rewrite to_digits_neg222222222.
  rewrite count_digits_222222222.
  reflexivity.
Qed.