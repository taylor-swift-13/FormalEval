Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

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

Definition problem_86_pre (s : string) : Prop := True.

Definition problem_86_spec (s s_out : string) : Prop :=
  s_out = anti_shuffle_impl s.

Example test_anti_shuffle_abcd :
  problem_86_spec "abcd" "abcd".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "abcd" "" *)
  (* c = 'a', not space, call anti_shuffle_aux "bcd" "a" *)
  (* anti_shuffle_aux "bcd" "a" *)
  (* c = 'b', not space, call anti_shuffle_aux "cd" "ba" *)
  (* anti_shuffle_aux "cd" "ba" *)
  (* c = 'c', not space, call anti_shuffle_aux "d" "cba" *)
  (* anti_shuffle_aux "d" "cba" *)
  (* c = 'd', not space, call anti_shuffle_aux "" "dcba" *)
  (* anti_shuffle_aux "" "dcba" => sort_chars "dcba" *)
  (* sort_chars "dcba" *)
  (* insert_char 'd' (sort_chars "cba") *)
  (* sort_chars "cba" = insert_char 'c' (sort_chars "ba") *)
  (* sort_chars "ba" = insert_char 'b' (sort_chars "a") *)
  (* sort_chars "a" = insert_char 'a' (sort_chars "") = "a" *)
  (* insert_char 'b' "a" *)
  (* 'b' = 98, 'a' = 97, 98 <= 97? no *)
  (* insert_char 'b' "a" = "a" ++ insert_char 'b' "" = "ab" *)
  (* insert_char 'c' "ab" *)
  (* 'c' = 99, 'a' = 97, 99 <= 97? no *)
  (* so "a" ++ insert_char 'c' "b" *)
  (* insert_char 'c' "b" *)
  (* 'c'=99, 'b'=98, 99 <= 98? no *)
  (* "b" ++ insert_char 'c' "" = "bc" *)
  (* so "a" ++ "bc" = "abc" *)
  (* insert_char 'd' "abc" *)
  (* 'd' = 100, 'a' = 97, 100 <= 97? no *)
  (* "a" ++ insert_char 'd' "bc" *)
  (* insert_char 'd' "bc" *)
  (* 'd'=100, 'b'=98, 100 <= 98? no *)
  (* "b" ++ insert_char 'd' "c" *)
  (* insert_char 'd' "c" *)
  (* 'd'=100, 'c'=99, 100 <= 99? no *)
  (* "c" ++ insert_char 'd' "" = "cd" *)
  (* "b" ++ "cd" = "bcd" *)
  (* "a" ++ "bcd" = "abcd" *)
  reflexivity.
Qed.