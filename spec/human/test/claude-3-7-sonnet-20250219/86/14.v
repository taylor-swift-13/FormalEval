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

Example test_anti_shuffle_This_is_a_test_dot :
  problem_86_spec "This is a test." "This is a .estt".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.

  (* Step 1: anti_shuffle_aux "This is a test." "" *)
  (* 'T' not space -> recurse with acc = "T" *)
  (* anti_shuffle_aux "his is a test." "T" *)

  (* 'h' not space -> acc = "hT" *)
  (* anti_shuffle_aux "is is a test." "hT" *)

  (* 'i' not space -> acc = "i hT" = "i hT"? No spaces, so String c acc *)
  (* Actually acc = String 'i' "hT" = "ihT" *)
  (* anti_shuffle_aux "s is a test." "ihT" *)

  (* 's' not space -> acc = "sihT" *)
  (* anti_shuffle_aux " is a test." "sihT" *)

  (* ' ' is space *)
  (* return sort_chars acc ++ " " ++ anti_shuffle_aux "is a test." EmptyString *)

  (* sort_chars "sihT" *)
  (* insertion sort as follows *)
  (* sort_chars "sihT" = insert_char 's' (sort_chars "ihT") *)

  (* sort_chars "ihT" = insert_char 'i' (sort_chars "hT") *)

  (* sort_chars "hT" = insert_char 'h' (sort_chars "T") *)

  (* sort_chars "T" = insert_char 'T' "" = "T" *)

  (* insert_char 'h' "T" : compare h and T *)
  (* nat_of_ascii 'h' = 104, 'T' = 84 *)
  (* 104 ≤ 84? no *)
  (* so String 'T' (insert_char 'h' "") = "Th" *)

  (* insert_char 'i' "Th" *)
  (* 'i' = 105, 'T' = 84 *)
  (* 105 ≤ 84? no *)
  (* String 'T' (insert_char 'i' "h") *)

  (* insert_char 'i' "h" *)
  (* 'i' = 105, 'h' = 104 *)
  (* 105 ≤ 104? no *)
  (* String 'h' (insert_char 'i' "") = "hi" *)

  (* so insert_char 'i' "h" = "hi" *)

  (* string is String 'T' "hi" = "Thi" *)

  (* insert_char 's' "Thi" *)
  (* 's' = 115, 'T' = 84 *)
  (* 115 ≤ 84? no *)
  (* String 'T' (insert_char 's' "hi") *)

  (* insert_char 's' "hi" *)
  (* 's' = 115, 'h' = 104 *)
  (* 115 ≤ 104? no *)
  (* String 'h' (insert_char 's' "i") *)

  (* insert_char 's' "i" *)
  (* 's' = 115, 'i' = 105 *)
  (* 115 ≤ 105? no *)
  (* String 'i' (insert_char 's' "") = "is" *)

  (* so insert_char 's' "i" = "is" *)

  (* so insert_char 's' "hi" = "his" *)

  (* so full string after insert_char 's' "Thi" = "This" *)

  (* sort_chars "sihT" = "This" *)

  (* anti_shuffle_aux "is a test." "" *)

  (* Next segment: "is a test." *)

  (* 'i' not space *)
  (* acc = "i" *)

  (* anti_shuffle_aux "s a test." "i" *)

  (* 's' not space *)
  (* acc = "s i" ("si") *)

  (* anti_shuffle_aux " a test." "si" *)

  (* ' ' is space *)
  (* return sort_chars "si" ++ " " ++ anti_shuffle_aux "a test." "" *)

  (* sort_chars "si" *)
  (* sort_chars 's' 'i' = insert_char 's' (sort_chars 'i') *)
  (* sort_chars "i" = insert_char 'i' "" = "i" *)
  (* insert_char 's' "i" *)
  (* 's' = 115 , 'i' = 105 *)
  (* 115 ≤ 105? no *)
  (* String 'i' (insert_char 's' "") = "is" *)

  (* sort_chars "si" = "is" *)

  (* anti_shuffle_aux "a test." "" *)

  (* 'a' not space *)
  (* acc = "a" *)
  (* anti_shuffle_aux " test." "a" *)

  (* ' ' is space *)
  (* return sort_chars "a" ++ " " ++ anti_shuffle_aux "test." "" *)

  (* sort_chars "a" = "a" *)

  (* anti_shuffle_aux "test." "" *)

  (* 't' not space acc = "t" *)
  (* anti_shuffle_aux "est." "t" *)

  (* 'e' not space acc = "e t" = "et" ? *)
  (* acc = String 'e' "t" = "et" *)
  (* anti_shuffle_aux "st." "et" *)

  (* 's' not space acc = "s et" = "set" ? *)
  (* acc = String 's' "et" = "set" *)
  (* anti_shuffle_aux "t." "set" *)

  (* 't' not space acc = "t set" = "tset" *)
  (* acc = String 't' "set" = "tset" *)
  (* anti_shuffle_aux "." "tset" *)

  (* '.' not space *)
  (* acc = String '.' "tset" = ".tset" *)
  (* anti_shuffle_aux EmptyString ".tset" *)

  (* EmptyString case: sort_chars ".tset" *)

  (* sort_chars ".tset" *)

  (* sort_chars = insert_char '.' (sort_chars "tset") *)

  (* sort_chars "tset" *)

  (* sort_chars 't' "set" *)

  (* sort_chars "set" *)

  (* sort_chars 's' "et" *)

  (* sort_chars "et" *)

  (* sort_chars 'e' "t" *)

  (* sort_chars "t" *)

  (* sort_chars "" = EmptyString *)

  (* insert_char 't' "" = "t" *)

  (* insert_char 'e' "t" *)
  (* 'e'=101, 't'=116 *)
  (* 101 ≤ 116? yes *)
  (* String 'e' "t" = "et" *)

  (* insert_char 's' "et" *)
  (* 's' = 115, 'e' = 101 *)
  (* 115 ≤ 101? no *)
  (* String 'e' (insert_char 's' "t") *)

  (* insert_char 's' "t" *)
  (* 's' = 115, 't' = 116 *)
  (* 115 ≤ 116? yes *)
  (* String 's' "t" = "st" *)

  (* so insert_char 's' "et" = "est" *)

  (* insert_char 't' "est" *)
  (* 't' = 116, 'e' = 101 *)
  (* 116 ≤ 101? no *)
  (* String 'e' (insert_char 't' "st") *)

  (* insert_char 't' "st" *)
  (* 't' = 116, 's' = 115 *)
  (* 116 ≤ 115? no *)
  (* String 's' (insert_char 't' "t") *)

  (* insert_char 't' "t" *)
  (* 't' = 116, 't' = 116 *)
  (* 116 ≤ 116? yes *)
  (* String 't' "t" = "tt" *)

  (* so insert_char 't' "t" = "tt" *)

  (* so insert_char 't' "st" = "stt" *)

  (* so insert_char 't' "est" = "estt" *)

  (* sort_chars "tset" = "estt" *)

  (* insert_char '.' "estt" *)
  (* '.'=46, 'e' = 101 *)
  (* 46 ≤ 101? yes *)
  (* String '.' "estt" = ".estt" *)

  (* sort_chars ".tset" = ".estt" *)

  reflexivity.
Qed.