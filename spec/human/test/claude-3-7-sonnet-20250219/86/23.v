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

Example test_anti_shuffle_lDQH :
  problem_86_spec "lDQH" "DHQl".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "lDQH" "" *)
  (* c = 'l', not space, call anti_shuffle_aux "DQH" "l" *)
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "DQH" "l" *)
  (* c = 'D', not space, call anti_shuffle_aux "QH" "Dl" *)
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "QH" "Dl" *)
  (* c = 'Q', not space, call anti_shuffle_aux "H" "QDl" *)
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "H" "QDl" *)
  (* c = 'H', not space, call anti_shuffle_aux "" "HQDl" *)
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "" "HQDl" = sort_chars "HQDl" *)
  (* sort_chars "HQDl" *)
  unfold sort_chars.
  simpl.
  (* insert_char 'H' (sort_chars "QDl") *)
  unfold sort_chars.
  simpl.
  (* insert_char 'H' (insert_char 'Q' (sort_chars "Dl")) *)
  unfold sort_chars.
  simpl.
  (* insert_char 'H' (insert_char 'Q' (insert_char 'D' (sort_chars "l"))) *)
  unfold sort_chars.
  simpl.
  (* insert_char 'H' (insert_char 'Q' (insert_char 'D' (insert_char 'l' (sort_chars "")))) *)
  unfold sort_chars.
  simpl.
  (* sort_chars "" = "" *)
  (* insert_char 'l' "" = "l" *)
  (* insert_char 'D' "l" *)
  (* nat_of_ascii 'D' = 68, nat_of_ascii 'l' = 108 *)
  (* 68 <= 108 = true, so insert_char 'D' "l" = String 'D' "l" = "Dl" *)
  (* insert_char 'Q' "Dl" *)
  (* nat_of_ascii 'Q' = 81, 'D' = 68 *)
  (* 81 <= 68 = false, so else: String 'D' (insert_char 'Q' "l") *)
  (* insert_char 'Q' "l" *)
  (* nat_of_ascii 'Q' = 81, 'l' = 108 *)
  (* 81 <= 108 = true, so String 'Q' "l" = "Ql" *)
  (* so insert_char 'Q' "Dl" = "DQl" *)
  (* insert_char 'H' "DQl" *)
  (* nat_of_ascii 'H' = 72, 'D' = 68 *)
  (* 72 <= 68 = false, else: String 'D' (insert_char 'H' "Ql") *)
  (* insert_char 'H' "Ql" *)
  (* nat_of_ascii 'H' = 72, 'Q' = 81 *)
  (* 72 <= 81 = true, so String 'H' "l" = "Hl" *)
  (* insert_char 'H' "Ql" = "Hl" *)
  (* insert_char 'H' "DQl" = "DHl" *)
  (* So the final string is "DHl" *)

  (* But above last step: insert_char 'H' "DQl" was computed as String 'D' (insert_char 'H' "Ql") 
     = "D" ++ "Hl" = "DHl" *)

  (* Hence, sort_chars "HQDl" = "DHQl" *)

  reflexivity.
Qed.