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

Example test_anti_shuffle_number :
  problem_86_spec "number" "bemnru".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.

  simpl.

  (* anti_shuffle_aux "number" "" *)
  (* first char 'n', not space, acc = "n" *)
  (* call anti_shuffle_aux "umber" "n" *)

  (* next char 'u', not space, acc = "un" *)
  (* call anti_shuffle_aux "mber" "u" + "n" = "un" *)

  (* char 'm', not space, acc = "mun" *)
  (* call anti_shuffle_aux "ber" "mun" *)

  (* char 'b', not space, acc = "bmun" *)
  (* call anti_shuffle_aux "er" "bmun" *)

  (* char 'e', not space, acc = "ebmun" *)
  (* call anti_shuffle_aux "r" "ebmun" *)

  (* char 'r', not space, acc = "rebmun" *)
  (* call anti_shuffle_aux "" "rebmun" *)

  (* now at EmptyString, return sort_chars "rebmun" *)

  (* sort_chars "rebmun" = insert_char 'r' (sort_chars "ebmun") *)
  (* sort_chars "ebmun" = insert_char 'e' (sort_chars "bmun") *)
  (* sort_chars "bmun" = insert_char 'b' (sort_chars "mun") *)
  (* sort_chars "mun" = insert_char 'm' (sort_chars "un") *)
  (* sort_chars "un" = insert_char 'u' (sort_chars "n") *)
  (* sort_chars "n" = insert_char 'n' (sort_chars "") = insert_char 'n' "" = "n" *)

  (* insert_char 'u' "n": nat_of_ascii 'u' = 117, 'n' = 110, 117 <= 110? false
     => else branch: "n" ++ "u" = "nu" *)

  (* insert_char 'm' "nu": 'm' = 109, 'n' = 110, 109 <=110? true
    => "m" ++ "nu" = "mnu" *)

  (* insert_char 'b' "mnu": 'b' = 98, 'm' = 109, 98 <=109? true
    => "b" ++ "mnu" = "bmnu" *)

  (* insert_char 'e' "bmnu": 'e' = 101, 'b' = 98, 101 <=98? false
    => else branch: 'b' ++ insert_char 'e' "mnu" *)

  (* insert_char 'e' "mnu": 'e' =101, 'm' =109, 101 <=109? true
    => "e" ++ "mnu" = "emnu" *)

  (* so above = "b" ++ "emnu" = "bemnu" *)

  (* insert_char 'r' "bemnu": 'r' =114, 'b' =98, 114 <=98? false
    => else branch: "b" ++ insert_char 'r' "emnu" *)

  (* insert_char 'r' "emnu": 'r' =114, 'e' =101, 114 <=101? false
    => else branch: 'e' ++ insert_char 'r' "mnu" *)

  (* insert_char 'r' "mnu": 'r' =114, 'm' =109, 114 <=109? false
    => else branch: 'm' ++ insert_char 'r' "nu" *)

  (* insert_char 'r' "nu": 'r' =114, 'n' =110, 114 <=110? false
    => else branch: 'n' ++ insert_char 'r' "u" *)

  (* insert_char 'r' "u": 'r' =114, 'u' =117, 114 <=117? true
    => "r" ++ "u" = "ru" *)

  (* working back up: 'n' ++ "ru" = "nru" *)
  (* 'm' ++ "nru"= "mnru" *)
  (* 'e' ++ "mnru"= "emnru" *)
  (* 'b' ++ "emnru"= "bemnru" *)

  reflexivity.
Qed.