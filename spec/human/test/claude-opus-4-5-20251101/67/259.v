Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.

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

Lemma string_to_nat_1 : string_to_nat "1" = 1.
Proof.
  unfold string_to_nat, string_to_nat_aux.
  unfold char_to_digit.
  simpl.
  reflexivity.
Qed.

Lemma string_to_nat_9 : string_to_nat "9" = 9.
Proof.
  unfold string_to_nat, string_to_nat_aux.
  unfold char_to_digit.
  simpl.
  reflexivity.
Qed.

Lemma string_concat_check : 
  ("1" ++ " apples and " ++ "9" ++ " oranges")%string = "1 apples and 9 oranges"%string.
Proof.
  simpl.
  reflexivity.
Qed.

Example problem_67_test : problem_67_spec "1 apples and 9 oranges" 20 10.
Proof.
  unfold problem_67_spec.
  exists 1, 9.
  split.
  - unfold parse_fruit_string.
    exists "1"%string, "9"%string.
    split.
    + exact string_to_nat_1.
    + split.
      * exact string_to_nat_9.
      * reflexivity.
  - simpl. reflexivity.
Qed.