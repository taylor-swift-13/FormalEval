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
  let d0 := p mod 10 in
  let p1 := p / 10 in
  let d1 := p1 mod 10 in
  let p2 := p1 / 10 in
  let d2 := p2 mod 10 in
  let p3 := p2 / 10 in
  let d3 := p3 mod 10 in
  let p4 := p3 / 10 in
  let d4 := p4 mod 10 in
  let p5 := p4 / 10 in
  let d5 := p5 mod 10 in
  let p6 := p5 / 10 in
  let d6 := p6 mod 10 in
  let p7 := p6 / 10 in
  let d7 := p7 mod 10 in
  let p8 := p7 / 10 in
  let d8 := p8 mod 10 in
  d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: nil.

Definition count_9_fours : nat * nat :=
  count_digits_acc (4::4::4::4::4::4::4::4::4::nil) (0%nat, 0%nat).

Example test_even_odd_count_444444444 : problem_155_spec 444444444 (9%nat, 0%nat).
Proof.
  unfold problem_155_spec.
  unfold even_odd_count_impl.
  native_compute.
  reflexivity.
Qed.