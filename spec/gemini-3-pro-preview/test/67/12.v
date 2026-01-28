Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_val (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_ints (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
      match curr with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_val c in
        match curr with
        | Some n => extract_ints s' (Some (n * 10 + d))
        | None => extract_ints s' (Some d)
        end
      else
        match curr with
        | Some n => n :: extract_ints s' None
        | None => extract_ints s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_ints s None in
  n - fold_right Z.add 0 nums.

Example fruit_distribution_test : fruit_distribution "0 apples and 0 oranges" 10 = 10.
Proof.
  compute.
  reflexivity.
Qed.