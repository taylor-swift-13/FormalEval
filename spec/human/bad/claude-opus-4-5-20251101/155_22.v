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

Definition count_digits_9 (l : list Z) : nat * nat :=
  match l with
  | d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: nil =>
      let e0 := if Z.even d0 then 1%nat else 0%nat in
      let o0 := if Z.even d0 then 0%nat else 1%nat in
      let e1 := if Z.even d1 then (e0 + 1)%nat else e0 in
      let o1 := if Z.even d1 then o0 else (o0 + 1)%nat in
      let e2 := if Z.even d2 then (e1 + 1)%nat else e1 in
      let o2 := if Z.even d2 then o1 else (o1 + 1)%nat in
      let e3 := if Z.even d3 then (e2 + 1)%nat else e2 in
      let o3 := if Z.even d3 then o2 else (o2 + 1)%nat in
      let e4 := if Z.even d4 then (e3 + 1)%nat else e3 in
      let o4 := if Z.even d4 then o3 else (o3 + 1)%nat in
      let e5 := if Z.even d5 then (e4 + 1)%nat else e4 in
      let o5 := if Z.even d5 then o4 else (o4 + 1)%nat in
      let e6 := if Z.even d6 then (e5 + 1)%nat else e5 in
      let o6 := if Z.even d6 then o5 else (o5 + 1)%nat in
      let e7 := if Z.even d7 then (e6 + 1)%nat else e6 in
      let o7 := if Z.even d7 then o6 else (o6 + 1)%nat in
      let e8 := if Z.even d8 then (e7 + 1)%nat else e7 in
      let o8 := if Z.even d8 then o7 else (o7 + 1)%nat in
      (e8, o8)
  | _ => (0%nat, 0%nat)
  end.

Lemma digits_222222221 : to_digits_9 (-222222221) = 1 :: 2 :: 2 :: 2 :: 2 :: 2 :: 2 :: 2 :: 2 :: nil.
Proof. native_compute. reflexivity. Qed.

Lemma count_result : count_digits_9 (1 :: 2 :: 2 :: 2 :: 2 :: 2 :: 2 :: 2 :: 2 :: nil) = (8%nat, 1%nat).
Proof. native_compute. reflexivity. Qed.

Example test_even_odd_count_neg222222221 : problem_155_spec (-222222221) (8%nat, 1%nat).
Proof.
  unfold problem_155_spec.
  unfold even_odd_count_impl.
  native_compute.
  reflexivity.
Qed.