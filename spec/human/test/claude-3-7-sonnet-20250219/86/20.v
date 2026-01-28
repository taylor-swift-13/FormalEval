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

Example test_anti_shuffle_Raccecar :
  problem_86_spec "Raccecar" "Raacccer".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.

  simpl.

  (* anti_shuffle_aux "Raccecar" "" *)
  (* first char: 'R', not space, acc = "R" *)
  (* rest "accecar" *)

  (* anti_shuffle_aux "accecar" "R" *)
  (* c = 'a', not space, acc = "aR" *)
  (* rest " ccecar" *)

  (* anti_shuffle_aux "ccecar" "aR" *)
  (* c = 'c', not space, acc = "c a R" = "caR" *)
  (* rest "cecar" *)

  (* anti_shuffle_aux "cecar" "caR" *)
  (* c = 'c', not space, acc = "c caR" = "ccaR" *)
  (* rest "ecar" *)

  (* anti_shuffle_aux "ecar" "ccaR" *)
  (* c = 'e', not space, acc = "e ccaR" = "eccaR" *)
  (* rest "car" *)

  (* anti_shuffle_aux "car" "eccaR" *)
  (* c = 'c', not space, acc = "c eccaR" = "ceccaR" *)
  (* rest "ar" *)

  (* anti_shuffle_aux "ar" "ceccaR" *)
  (* c = 'a', not space, acc = "a ceccaR" = "aceccaR" *)
  (* rest "r" *)

  (* anti_shuffle_aux "r" "aceccaR" *)
  (* c = 'r', not space, acc = "r aceccaR" = "raceccaR" *)
  (* rest "" *)

  (* anti_shuffle_aux "" "raceccaR" *)
  (* Return sort_chars acc = sort_chars "raceccaR" *)

  (* sort_chars "raceccaR" sorts letters in ascending order *)

  (* Convert the string to list of ascii codes for order check:
     letters: r(114), a(97), c(99), e(101), c(99), c(99), a(97), R(82)

     Sorting ascending: R(82), a(97), a(97), c(99), c(99), c(99), e(101), r(114)
     String: "Raacccer" *)

  reflexivity.
Qed.