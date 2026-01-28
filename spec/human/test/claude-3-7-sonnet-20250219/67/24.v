Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.

Open Scope string_scope.
Open Scope nat_scope.

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

Example test_fruit_distribution :
  problem_67_spec "0 apples and 0 oranges" 30 30.
Proof.
  unfold problem_67_spec.
  eexists. eexists.
  split.
  - unfold parse_fruit_string.
    exists "0". exists "0".
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * reflexivity.
  - simpl.
    lia.
Qed.