Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint to_digits_fuel (n fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
    if (n <? 10)%nat then
      [n]
    else
      (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then [0] else to_digits_fuel n n.

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

Definition circular_shift_impl (x : nat) (shift : nat) : string :=
  let digits := to_digits x in
  let len := length digits in
  if (x =? 0)%nat then
    "0"
  else
    if (len <? shift)%nat then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len in
      if (effective_shift =? 0)%nat then
        from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).

Definition problem_65_pre (x : nat) (shift : nat) : Prop := True.

Definition problem_65_spec (x : nat) (shift : nat) (result : string) : Prop :=
  result = circular_shift_impl x shift.

Example circular_shift_test_100_2 :
  problem_65_spec (Z.to_nat 100) (Z.to_nat 2) "001".
Proof.
  unfold problem_65_spec, circular_shift_impl.

  (* Simplify inputs *)
  rewrite <- (Z2Nat.id 100) at 1 by lia.
  rewrite <- (Z2Nat.id 2) at 1 by lia.

  (* Compute digits = to_digits 100 *)
  unfold to_digits.
  rewrite Nat.eqb_neq.
  - (* 100 <> 0 *)
    simpl.
    (* to_digits_fuel 100 100 = [1;0;0] *)
    assert (to_digits_fuel 100 100 = [1; 0; 0]) as Hdigits.
    {
      clear.
      induction 100 as [|f IH] using nat_ind2 with (P := fun n => to_digits_fuel 100 n = [1;0;0]).
      - simpl. reflexivity.
      - simpl.
        (* 100 <? 10 = false *)
        rewrite Nat.ltb_ge by lia.
        simpl.
        rewrite IH; try lia.
        reflexivity.
      - (* base case *)
        simpl.
        rewrite Nat.ltb_ge by lia.
        reflexivity.
    }
    rewrite Hdigits.
    simpl.

    (* length digits = 3 *)
    rewrite Nat.ltb_ge; try lia.
    simpl.

    (* Calculate effective_shift = 2 mod 3 = 2 *)
    remember (2 mod 3) as eff_shift eqn:Heff.
    assert (eff_shift = 2) by (subst; lia).
    subst eff_shift.
    rewrite Nat.eqb_neq; [|lia].
    simpl.

    (* split_point = 3 - 2 = 1 *)
    (* new_head = skipn 1 [1;0;0] = [0;0] *)
    (* new_tail = firstn 1 [1;0;0] = [1] *)
    (* from_digits_to_string new_head ++ new_tail = from_digits_to_string [0;0;1] = "001" *)

    unfold from_digits_to_string, digit_to_string.
    simpl.
    reflexivity.
  - lia.
Qed.