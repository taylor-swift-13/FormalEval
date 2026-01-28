Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope string_scope.

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Fixpoint insert_char (c : ascii) (s : string) : string :=
  match s with
  | EmptyString => String c EmptyString
  | String h t =>
      if Nat.leb (nat_of_ascii c) (nat_of_ascii h) then
        String c s
      else
        String h (insert_char c t)
  end.

Fixpoint sort_chars (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t => insert_char h (sort_chars t)
  end.

Fixpoint anti_shuffle_aux (s : string) (acc : string) : string :=
  match s with
  | EmptyString => sort_chars acc
  | String c rest =>
      if is_space_bool c then
        (sort_chars acc) ++ (String c EmptyString) ++ (anti_shuffle_aux rest EmptyString)
      else
        anti_shuffle_aux rest (String c acc)
  end.

Definition anti_shuffle_impl (s : string) : string :=
  anti_shuffle_aux s EmptyString.

Example test_anti_shuffle_hello : anti_shuffle_impl "hello" = "ehllo".
Proof.
  unfold anti_shuffle_impl.
  simpl.
  unfold is_space_bool.
  destruct (ascii_dec "h" " ")%char.
  - inversion e.
  - simpl.
    destruct (ascii_dec "e" " ")%char.
    + inversion e.
    + simpl.
      destruct (ascii_dec "l" " ")%char.
      * inversion e.
      * simpl.
        destruct (ascii_dec "l" " ")%char.
        -- inversion e.
        -- simpl.
           destruct (ascii_dec "o" " ")%char.
           ++ inversion e.
           ++ simpl.
              reflexivity.
Qed.