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

Definition to_digits_small (n : Z) : list Z :=
  let p := Z.abs n in
  if p =? 0 then nil
  else let d0 := p mod 10 in
       let p1 := p / 10 in
       if p1 =? 0 then d0 :: nil
       else let d1 := p1 mod 10 in
            let p2 := p1 / 10 in
            if p2 =? 0 then d0 :: d1 :: nil
            else let d2 := p2 mod 10 in
                 let p3 := p2 / 10 in
                 if p3 =? 0 then d0 :: d1 :: d2 :: nil
                 else let d3 := p3 mod 10 in
                      let p4 := p3 / 10 in
                      if p4 =? 0 then d0 :: d1 :: d2 :: d3 :: nil
                      else let d4 := p4 mod 10 in
                           let p5 := p4 / 10 in
                           if p5 =? 0 then d0 :: d1 :: d2 :: d3 :: d4 :: nil
                           else let d5 := p5 mod 10 in
                                let p6 := p5 / 10 in
                                if p6 =? 0 then d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: nil
                                else let d6 := p6 mod 10 in
                                     let p7 := p6 / 10 in
                                     if p7 =? 0 then d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: nil
                                     else let d7 := p7 mod 10 in
                                          let p8 := p7 / 10 in
                                          if p8 =? 0 then d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: nil
                                          else let d8 := p8 mod 10 in
                                               d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: nil.

Definition even_odd_count_small (num : Z) : nat * nat :=
  count_digits_acc (to_digits_small num) (0%nat, 0%nat).

Example test_even_odd_count_444444442 : even_odd_count_small 444444442 = (9%nat, 0%nat).
Proof.
  native_compute.
  reflexivity.
Qed.

Example test_even_odd_count_444444442_spec : problem_155_spec 444444442 (9%nat, 0%nat).
Proof.
  unfold problem_155_spec.
  unfold even_odd_count_impl.
  native_compute.
  reflexivity.
Qed.