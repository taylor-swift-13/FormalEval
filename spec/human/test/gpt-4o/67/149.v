Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.
Open Scope Z_scope.

Definition char_to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - nat_of_ascii "0"%char).

Fixpoint string_to_Z_aux (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c s' => string_to_Z_aux s' (acc * 10 + char_to_digit c)
  end.

Definition string_to_Z (s : string) : Z :=
  string_to_Z_aux s 0.

Definition parse_fruit_string (s : string) (apples oranges : Z) : Prop :=
  exists s_apples s_oranges,
    apples = string_to_Z s_apples /\
    oranges = string_to_Z s_oranges /\
    s = (s_apples ++ " apples and " ++ s_oranges ++ " oranges")%string.

Definition problem_67_pre (s : string) (n : Z) : Prop := True.

Definition problem_67_spec (s : string) (n : Z) (ret : Z) : Prop :=
  exists apples oranges,
    parse_fruit_string s apples oranges /\
    ret = n - (apples + oranges).

Example example_proof :
  problem_67_spec "15 apples and 8 oranges" 28 5.
Proof.
  unfold problem_67_spec.
  exists 15, 8.
  split.
  - unfold parse_fruit_string.
    exists "15", "8".
    split; [reflexivity|].
    split; [reflexivity|].
    reflexivity.
  - simpl. compute. reflexivity.
Qed.