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

Example test_anti_shuffle_12345 :
  problem_86_spec "12345" "12345".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.
  (* anti_shuffle_aux "12345" "" *)
  (* Process '1': not space, acc = "1" "" *)
  (* anti_shuffle_aux "2345" "1" *)
  unfold is_space_bool.
  simpl.
  (* process '2': not space, acc = "21" *)
  (* anti_shuffle_aux "345" "21" *)
  unfold is_space_bool.
  simpl.
  (* process '3': not space, acc = "321" *)
  (* anti_shuffle_aux "45" "321" *)
  unfold is_space_bool.
  simpl.
  (* process '4': not space, acc = "4321" *)
  (* anti_shuffle_aux "5" "4321" *)
  unfold is_space_bool.
  simpl.
  (* process '5': not space, acc = "54321" *)
  (* anti_shuffle_aux "" "54321" *)
  unfold is_space_bool.
  simpl.
  (* now EmptyString -> sort_chars acc = sort_chars "54321" *)
  (* sort_chars "54321" = insert_char '5' (sort_chars "4321") *)
  (* similarly insert_char for '4','3','2','1' *)
  (* inserting each in order results in "12345" *)
  reflexivity.
Qed.