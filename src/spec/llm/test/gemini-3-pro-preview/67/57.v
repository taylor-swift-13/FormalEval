Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers_aux (s : string) (cur : option Z) : list Z :=
  match s with
  | EmptyString =>
      match cur with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := to_digit c in
        match cur with
        | Some n => extract_numbers_aux s' (Some (n * 10 + d))
        | None => extract_numbers_aux s' (Some d)
        end
      else
        match cur with
        | Some n => n :: extract_numbers_aux s' None
        | None => extract_numbers_aux s' None
        end
  end.

Definition extract_numbers (s : string) : list Z :=
  extract_numbers_aux s None.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - fold_right Z.add 0 (extract_numbers s).

Example check_fruit_distribution : fruit_distribution "10 apples and 0 oranges" 29 = 19.
Proof.
  vm_compute.
  reflexivity.
Qed.