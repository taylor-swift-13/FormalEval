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

Example test_anti_shuffle_hello :
  problem_86_spec "hello" "ehllo".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "hello" "" *)
  (* c = 'h', not space *)
  (* call anti_shuffle_aux "ello" "h" *)
  (* c = 'e', not space *)
  (* call anti_shuffle_aux "llo" "eh" *)
  (* c = 'l', not space *)
  (* call anti_shuffle_aux "lo" "leh" *)
  (* c = 'l', not space *)
  (* call anti_shuffle_aux "o" "lleh" *)
  (* c = 'o', not space *)
  (* call anti_shuffle_aux "" "olleh" *)
  (* now sort_chars "olleh" *)
  (* sort_chars "olleh" = insert_char 'o'(sort_chars "lleh") *)
  (* sort_chars "lleh" = insert_char 'l'(sort_chars "leh") *)
  (* sort_chars "leh" = insert_char 'l'(sort_chars "eh") *)
  (* sort_chars "eh" = insert_char 'e'(sort_chars "h") *)
  (* sort_chars "h" = insert_char 'h' "" = "h" *)
  (* insert_char 'e' "h": 'e' = 101, 'h' = 104, 101 <= 104 => String 'e' "h" = "eh" *)
  (* insert_char 'l' "eh": 'l' = 108, 'e' = 101, 108 <= 101? false, so else branch: "e" ++ insert_char 'l' "h" *)
  (* insert_char 'l' "h": 'l'=108, 'h'=104, 108 <= 104? false, else: "h"++ insert_char 'l' "" = "hl" *)
  (* so insert_char 'l' "eh" = "ehl" *)
  (* insert_char 'l' "ehl": 'l'=108, 'e' =101, 108 <= 101? false, else: "e"++ insert_char 'l' "hl" *)
  (* insert_char 'l' "hl": 'l'=108, 'h'=104, 108 <=104? false, else "h" ++insert_char 'l' "l" *)
  (* insert_char 'l' "l": 'l'=108, 'l'=108, 108 <=108 true, so String 'l' "l" = "ll" *)
  (* insert_char 'l' "hl" = "hll" *)
  (* insert_char 'l' "ehl" = "ehll" *)
  (* insert_char 'o' "ehll": 'o'=111, 'e'=101, 111 <= 101? false, else "e" ++ insert_char 'o' "hll"*)
  (* insert_char 'o' "hll": 'o'=111, 'h'=104, 111 <=104? false, else "h" ++ insert_char 'o' "ll" *)
  (* insert_char 'o' "ll": 'o'=111, 'l'=108, 111 <=108? false, else "l" ++ insert_char 'o' "l" *)
  (* insert_char 'o' "l": 'o'=111, 'l' =108, 111 <=108? false, else "l" ++ insert_char 'o' "" *)
  (* insert_char 'o' "" = "o" *)
  (* So insert_char 'o' "l" = "lo" *)
  (* insert_char 'o' "ll" = "llo" *)
  (* insert_char 'o' "hll" = "hllo" *)
  (* insert_char 'o' "ehll" = "ehllo" *)
  reflexivity.
Qed.