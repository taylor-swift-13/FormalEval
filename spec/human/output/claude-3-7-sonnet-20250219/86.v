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

Example test_anti_shuffle_Hi :
  problem_86_spec "Hi" "Hi".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.

  (* evaluate anti_shuffle_aux "Hi" "" *)
  simpl.

  (* string "Hi" = String "H" (String "i" EmptyString).
     The function anti_shuffle_aux processes the first character 'H' (not space),
     so it calls anti_shuffle_aux on rest "i" with acc = "H" "" => "H" *)
  
  (* anti_shuffle_aux (String "H" (String "i" EmptyString)) EmptyString *)
  (* first c = "H", is_space_bool "H" = false *)
  (* so call anti_shuffle_aux (String "i" EmptyString) (String "H" EmptyString) *)

  (* anti_shuffle_aux (String "i" EmptyString) (String "H" EmptyString) *)
  (* c = "i", not space *)
  (* call anti_shuffle_aux EmptyString (String "i" (String "H" EmptyString)) *)

  (* Note: acc is built as String c acc, so acc = "iH" *)

  (* anti_shuffle_aux EmptyString (String "iH" EmptyString) *)
  (* match on EmptyString: return sort_chars acc = sort_chars "iH" *)

  (* sort_chars "iH" = insert_char 'i' (sort_chars "H") *)
  (* sort_chars "H" = insert_char 'H' (sort_chars "") = insert_char 'H' "" = "H" *)
  (* insert_char 'i' "H" *)
  (* nat_of_ascii 'i' = 105, nat_of_ascii 'H' = 72 *)
  (* 105 <= 72? false *)
  (* So go to else branch: String 'H' (insert_char 'i' "") = "H" ++ "i" = "Hi" *)

  (* So sort_chars "iH" = "Hi" *)
  reflexivity.
Qed.