Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_sum (s : string) (cur : option Z) (acc : Z) : Z :=
  match s with
  | EmptyString =>
      match cur with
      | Some v => acc + v
      | None => acc
      end
  | String c rest =>
      if is_digit c then
        let d := to_digit c in
        match cur with
        | Some v => parse_sum rest (Some (v * 10 + d)) acc
        | None => parse_sum rest (Some d) acc
        end
      else
        match cur with
        | Some v => parse_sum rest None (acc + v)
        | None => parse_sum rest None acc
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - parse_sum s None 0.

Example fruit_distribution_example : fruit_distribution "7 apples and 8 oranges" 15 = 0.
Proof.
  compute.
  reflexivity.
Qed.