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

Example test_anti_shuffle_Raceca :
  problem_86_spec "Raceca" "Raacce".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.

  (* anti_shuffle_aux "Raceca" "" *)
  (* "Raceca" = String 'R' (String 'a' (String 'c' (String 'e' (String 'c' (String 'a' EmptyString))))) *)
  (* is_space_bool 'R' = false *)
  (* call anti_shuffle_aux (String 'a' (String 'c' (String 'e' (String 'c' (String 'a' EmptyString)))) ) (String 'R' "") *)

  (* anti_shuffle_aux "aceca" "R" *)
  (* 'a' not space => anti_shuffle_aux "ceca" (String 'a' "R") = acc = "aR" *)
  
  (* anti_shuffle_aux "ceca" "aR" *)
  (* 'c' not space => acc = "c aR" *)
  (* anti_shuffle_aux "eca" (String 'c' "aR") = "c aR" *)

  (* anti_shuffle_aux "eca" "c aR" *)
  (* 'e' not space => acc = "e c aR" *)
  (* anti_shuffle_aux "ca" (String 'e' "c aR") *)

  (* anti_shuffle_aux "ca" "e c aR" *)
  (* 'c' not space => acc = "c e c a R" *)
  (* anti_shuffle_aux "a" (String 'c' "e c aR") *)

  (* anti_shuffle_aux "a" "c e c a R" *)
  (* 'a' not space => acc = "a c e c a R" *)
  (* anti_shuffle_aux "" (String 'a' "c e c aR") *)

  (* anti_shuffle_aux "" "a c e c a R" *)
  (* return sort_chars "acecaR" (acc reversed) *)

  (* sort_chars "acecaR" *)

  (* sort_chars (String 'a' (String 'c' (String 'e' (String 'c' (String 'a' (String 'R' EmptyString)))))) *)

  (* insert_char 'a' (sort_chars "cecaR") *)
  (* sort_chars "cecaR" = insert_char 'c' (sort_chars "ecaR") *)
  (* sort_chars "ecaR" = insert_char 'e' (sort_chars "caR") *)
  (* sort_chars "caR" = insert_char 'c' (sort_chars "aR") *)
  (* sort_chars "aR" = insert_char 'a' (sort_chars "R") *)
  (* sort_chars "R" = insert_char 'R' "" = "R" *)

  (* sort_chars "aR" *)
  (* insert_char 'a' "R" *)
  (* nat_of_ascii 'a' = 97, 'R' = 82, 97 <= 82? false *)
  (* else branch: String 'R' (insert_char 'a' "") = "Ra" *)

  (* sort_chars "caR" *)
  (* insert_char 'c' "Ra" *)
  (* 'c' = 99, 'R' = 82, 99 <= 82? false *)
  (* else String 'R' (insert_char 'c' "a") *)
  (* insert_char 'c' "a" *)
  (* 'c' = 99, 'a' = 97, 99 <= 97? false *)
  (* else String 'a' (insert_char 'c' "") = "ac" *)
  (* so insert_char 'c' "a" = "ac" *)
  (* so overall: String 'R' "ac" = "Rac" *)

  (* sort_chars "ecaR" *)
  (* insert_char 'e' "Rac" *)
  (* 'e' = 101, 'R' = 82, 101<=82? false *)
  (* else String 'R' (insert_char 'e' "ac") *)
  (* insert_char 'e' "ac" *)
  (* 'e'(101) vs 'a'(97): 101 <= 97? no *)
  (* else String 'a' (insert_char 'e' "c") *)
  (* insert_char 'e' "c" *)
  (* 'e'(101) vs 'c'(99): 101 <= 99? no *)
  (* else String 'c' (insert_char 'e' "") = "ce" *)
  (* so insert_char 'e' "c" = "ce" *)
  (* so insert_char 'e' "ac" = "ace" *)
  (* so overall: String 'R' "ace" = "Race" *)

  (* sort_chars "cecaR" *)
  (* from above "Rac" *)
  (* We missed re-application of insert_char 'c' after initial sort *)
  (* Actually, sort_chars "cecaR" = insert_char 'c' (sort_chars "ecaR") *)
  (* We just computed sort_chars "ecaR" = "Race" *)
  (* insert_char 'c' "Race" *)
  (* 'c'(99) vs 'R'(82): 99 <= 82? no *)
  (* else String 'R' (insert_char 'c' "ace") *)
  (* insert_char 'c' "ace" *)
  (* compare 'c'(99) with 'a'(97): 99 <= 97? no *)
  (* else String 'a' (insert_char 'c' "ce") *)
  (* insert_char 'c' "ce" *)
  (* 'c'(99) vs 'c'(99): 99 <= 99? yes *)
  (* so String 'c' "ce" = "cce" *)
  (* so insert_char 'c' "ce" = "cce" *)
  (* insert_char 'c' "ace" = "acc e" *)
  (* so String 'a' "cce" = "acce" *)
  (* so String 'R' "acce" = "Racce" *)

  (* Now sort_chars "cecaR" = "Racce" *)

  (* Finally, insert_char 'a' "Racce" *)
  (* 'a'(97) vs 'R'(82): 97 <= 82? no *)
  (* else String 'R' (insert_char 'a' "acce") *)
  (* insert_char 'a' "acce" *)
  (* 'a'(97) vs 'a'(97): 97 <= 97? yes *)
  (* so String 'a' "acce" = "aacce" *)
  (* so insert_char 'a' "acce" = "aacce" *)
  (* so final string: String 'R' "aacce" = "Raacce" *)

  reflexivity.
Qed.