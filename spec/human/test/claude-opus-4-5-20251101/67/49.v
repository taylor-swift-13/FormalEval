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

Lemma string_to_nat_0 : string_to_nat "0" = 0.
Proof.
  unfold string_to_nat, string_to_nat_aux.
  unfold char_to_digit.
  simpl.
  reflexivity.
Qed.

Lemma string_to_nat_1 : string_to_nat "1" = 1.
Proof.
  unfold string_to_nat, string_to_nat_aux.
  unfold char_to_digit.
  simpl.
  reflexivity.
Qed.

Lemma string_concat_check : 
  ("0" ++ " apples and " ++ "1" ++ " oranges")%string = "0 apples and 1 oranges"%string.
Proof.
  simpl.
  reflexivity.
Qed.

Example problem_67_test : problem_67_spec "0 apples and 1 oranges" 4 3.
Proof.
  unfold problem_67_spec.
  exists 0, 1.
  split.
  - unfold parse_fruit_string.
    exists "0"%string, "1"%string.
    split.
    + exact string_to_nat_0.
    + split.
      * exact string_to_nat_1.
      * reflexivity.
  - simpl. reflexivity.
Qed.