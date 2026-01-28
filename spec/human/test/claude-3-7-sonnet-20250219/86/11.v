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

Example test_anti_shuffle_Racecar :
  problem_86_spec "Racecar" "Raaccer".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.

  (* anti_shuffle_aux (String "R" (String "a" (String "c" (String "e" (String "c" (String "a" (String "r" EmptyString))))))) EmptyString *)

  (* Processing 'R', not space *)
  (* anti_shuffle_aux (String "a" (String "c" (String "e" (String "c" (String "a" (String "r" EmptyString)))))) (String "R" EmptyString) *)

  (* Processing 'a', not space *)
  (* anti_shuffle_aux (String "c" (String "e" (String "c" (String "a" (String "r" EmptyString))))) (String "a" (String "R" EmptyString)) *)

  (* Processing 'c', not space *)
  (* anti_shuffle_aux (String "e" (String "c" (String "a" (String "r" EmptyString)))) (String "c" (String "a" (String "R" EmptyString))) *)

  (* Processing 'e', not space *)
  (* anti_shuffle_aux (String "c" (String "a" (String "r" EmptyString))) (String "e" (String "c" (String "a" (String "R" EmptyString)))) *)

  (* Processing 'c', not space *)
  (* anti_shuffle_aux (String "a" (String "r" EmptyString)) (String "c" (String "e" (String "c" (String "a" (String "R" EmptyString)))))*)

  (* Processing 'a', not space *)
  (* anti_shuffle_aux (String "r" EmptyString) (String "a" (String "c" (String "e" (String "c" (String "a" (String "R" EmptyString))))) *)

  (* Processing 'r', not space *)
  (* anti_shuffle_aux EmptyString (String "r" (String "a" (String "c" (String "e" (String "c" (String "a" (String "R" EmptyString)))))) *)

  (* Now s = EmptyString, so return sort_chars acc *)

  (* acc = "r a c e c a R" with cons String c acc builds acc in reverse order *)

  (* acc string is String 'r' (String 'a' (String 'c' (String 'e' (String 'c' (String 'a' (String 'R' EmptyString)))))) *)

  (* So acc = "racecaR" (note the case and order due to how acc is built) *)

  (* sort_chars "racecaR" *)

  (* sort_chars = insert_char 'r' (sort_chars "acecaR") *)
  (* sort_chars "acecaR" = insert_char 'a' (sort_chars "cecaR") *)
  (* sort_chars "cecaR" = insert_char 'c' (sort_chars "ecaR") *)
  (* sort_chars "ecaR" = insert_char 'e' (sort_chars "caR") *)
  (* sort_chars "caR" = insert_char 'c' (sort_chars "aR") *)
  (* sort_chars "aR" = insert_char 'a' (sort_chars "R") *)
  (* sort_chars "R" = insert_char 'R' (sort_chars "") = insert_char 'R' "" = "R" *)

  (* Insert 'a' into "R" *)

  (* nat_of_ascii 'a' = 97, nat_of_ascii 'R' = 82 *)

  (* 97 <= 82 ? false -> else -> String 'R' (insert_char 'a' "") = "Ra" *)

  (* Insert 'c' into "Ra" *)

  (* nat_of_ascii 'c' = 99, nat_of_ascii 'R' = 82 *)

  (* 99 <= 82 ? false -> else -> String 'R' (insert_char 'c' "a") *)

  (* insert_char 'c' "a": *)

  (* nat_of_ascii 'c' = 99, nat_of_ascii 'a' = 97 *)

  (* 99 <= 97 ? false -> else -> String 'a' (insert_char 'c' "") = "a c" *)

  (* So insert_char 'c' "a" = "ac" *)

  (* So insert_char 'c' "Ra" = "Rac" *)

  (* Insert 'e' into "Rac" *)

  (* nat_of_ascii 'e' = 101, 'R' = 82 *)

  (* 101 <= 82? false -> else -> String 'R' (insert_char 'e' "ac") *)

  (* insert_char 'e' "ac": *)

  (* nat_of_ascii 'e' = 101, 'a' = 97 *)

  (* 101 <= 97? false -> else -> String 'a' (insert_char 'e' "c") *)

  (* insert_char 'e' "c": *)

  (* nat_of_ascii 'e' = 101, 'c' = 99 *)

  (* 101 <= 99? false -> else -> String 'c' (insert_char 'e' "") = "c e" *)

  (* So insert_char 'e' "c" = "ce" *)

  (* insert_char 'e' "ac" = "ace" *)

  (* insert_char 'e' "Rac" = "Race" *)

  (* Insert 'c' into "Race" *)

  (* nat_of_ascii 'c' = 99, 'R' = 82 *)

  (* 99 <= 82? false -> else -> String 'R' (insert_char 'c' "ace") *)

  (* insert_char 'c' "ace": *)

  (* nat_of_ascii 'c' = 99, 'a' = 97 *)

  (* 99 <= 97? false -> else -> String 'a' (insert_char 'c' "ce") *)

  (* insert_char 'c' "ce": *)

  (* nat_of_ascii 'c' = 99, 'c' = 99 *)

  (* 99 <= 99? true -> String 'c' "ce" = "cce" *)

  (* insert_char 'c' "ce" = "cce" *)

  (* insert_char 'c' "ace" = "acce" *)

  (* insert_char 'c' "Race" = "Racce" *)

  (* Insert 'a' into "Racce" *)

  (* nat_of_ascii 'a' = 97, 'R' = 82 *)

  (* 97 <= 82? false -> else -> String 'R' (insert_char 'a' "acce") *)

  (* insert_char 'a' "acce": *)

  (* nat_of_ascii 'a' = 97, 'a' = 97 *)

  (* 97 <= 97? true -> String 'a' "acce" = "aacce" *)

  (* insert_char 'a' "acce" = "aacce" *)

  (* insert_char 'a' "Racce" = "Raacce" *)

  (* Insert 'r' into "Raacce" *)

  (* nat_of_ascii 'r' = 114, 'R' = 82 *)

  (* 114 <= 82? false -> else -> String 'R' (insert_char 'r' "aacce") *)

  (* insert_char 'r' "aacce": *)

  (* nat_of_ascii 'r' = 114, 'a' = 97 *)

  (* 114 <= 97? false -> else -> String 'a' (insert_char 'r' "acce") *)

  (* insert_char 'r' "acce": *)

  (* nat_of_ascii 'r' = 114, 'a' = 97 *)

  (* 114 <= 97? false -> else -> String 'a' (insert_char 'r' "cce") *)

  (* insert_char 'r' "cce": *)

  (* nat_of_ascii 'r' = 114, 'c' = 99 *)

  (* 114 <= 99? false -> else -> String 'c' (insert_char 'r' "ce") *)

  (* insert_char 'r' "ce": *)

  (* nat_of_ascii 'r' = 114, 'c' = 99 *)

  (* 114 <= 99? false -> else -> String 'c' (insert_char 'r' "e") *)

  (* insert_char 'r' "e": *)

  (* nat_of_ascii 'r' = 114, 'e' = 101 *)

  (* 114 <= 101? false -> else -> String 'e' (insert_char 'r' "") *)

  (* insert_char 'r' "" = "r" *)

  (* So insert_char 'r' "e" = "er" *)

  (* insert_char 'r' "ce" = "cer" *)

  (* insert_char 'r' "cce" = "ccer" *)

  (* insert_char 'r' "acce" = "accer" *)

  (* insert_char 'r' "aacce" = "aaccer" *)

  (* insert_char 'r' "Raacce" = "Raaccer" *)

  reflexivity.
Qed.