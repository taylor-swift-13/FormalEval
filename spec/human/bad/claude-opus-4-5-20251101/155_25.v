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

Definition to_digits_9 (n : Z) : list Z :=
  let p := Z.abs n in
  (p mod 10) ::
  ((p / 10) mod 10) ::
  ((p / 100) mod 10) ::
  ((p / 1000) mod 10) ::
  ((p / 10000) mod 10) ::
  ((p / 100000) mod 10) ::
  ((p / 1000000) mod 10) ::
  ((p / 10000000) mod 10) ::
  ((p / 100000000) mod 10) :: nil.

Lemma digits_of_222222224 : to_digits_9 (-222222224) = 4::2::2::2::2::2::2::2::2::nil.
Proof. reflexivity. Qed.

Lemma count_digits_222222224 : count_digits_acc (4::2::2::2::2::2::2::2::2::nil) (0%nat, 0%nat) = (9%nat, 0%nat).
Proof. reflexivity. Qed.

Example test_even_odd_count_neg222222224 : problem_155_spec (-222222224) (9%nat, 0%nat).
Proof.
  unfold problem_155_spec.
  unfold even_odd_count_impl.
  native_compute.
  reflexivity.
Qed.