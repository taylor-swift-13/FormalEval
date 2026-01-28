Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.

Definition char_to_digit (c : ascii) : nat :=
  nat_of_ascii c - nat_of_ascii "0"%char.

Fixpoint string_to_nat_aux (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' => string_to_nat_aux s' (acc * 10 + char_to_digit c)
  end.

Definition string_to_nat (s : string) : nat :=
  string_to_nat_aux s 0.

Definition parse_fruit_string (s : string) (apples oranges : nat) : Prop :=
  exists s_apples s_oranges,
    apples = string_to_nat s_apples /\
    oranges = string_to_nat s_oranges /\
    s = (s_apples ++ " apples and " ++ s_oranges ++ " oranges")%string.

Definition problem_67_pre (s : string) (n : nat) : Prop := True.

Definition problem_67_spec (s : string) (n : nat) (ret : nat) : Prop :=
  exists apples oranges,
    parse_fruit_string s apples oranges /\
    ret = n - (apples + oranges).

Example fruit_distribution_test :
  problem_67_spec ("50 apples and 50 oranges")%string 100%nat 0%nat.
Proof.
  unfold problem_67_spec.
  exists (string_to_nat "50"%string), (string_to_nat "50"%string).
  split.
  - unfold parse_fruit_string.
    exists "50"%string, "50"%string.
    repeat split; simpl; reflexivity.
  - simpl. reflexivity.
Qed.