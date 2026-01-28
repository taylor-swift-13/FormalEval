Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_of_string s'
  end.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint sum_nums (l : list ascii) (curr : option Z) (acc : Z) : Z :=
  match l with
  | [] => match curr with
          | Some n => acc + n
          | None => acc
          end
  | c :: rest =>
      if is_digit c then
        let d := digit_to_Z c in
        match curr with
        | Some n => sum_nums rest (Some (n * 10 + d)) acc
        | None => sum_nums rest (Some d) acc
        end
      else
        match curr with
        | Some n => sum_nums rest None (acc + n)
        | None => sum_nums rest None acc
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let l := list_of_string s in
  n - sum_nums l None 0.

Example test_fruit_distribution: fruit_distribution "3 apples and 5 oranges" 14 = 6.
Proof.
  vm_compute.
  reflexivity.
Qed.