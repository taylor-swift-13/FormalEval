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

Example test_anti_shuffle_Quick_brown_fox :
  problem_86_spec "Quick brown fox" "Qciku bnorw fox".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.
  simpl.
  (* Step-by-step evaluation unfolds:
     "Quick brown fox" = String 'Q' (String 'u' (String 'i' (String 'c' (String 'k' (String ' ' (String 'b' (String 'r' (String 'o' (String 'w' (String 'n' (String ' ' (String 'f' (String 'o' (String 'x' EmptyString))))))))))))) *)

  (* Process characters:
     - Collect non-space characters at start into acc reversed
     - On space, sort acc, output sorted acc + space + recursive call with acc reset *)

  (* First space at 6th character *)
  (* acc after first space "Quick": characters collected backwards = "kciuQ" *)

  (* sort_chars rev "kciuQ" = sort_chars "kciuQ" = "Qciku" *)

  (* Then space output " " *)

  (* Next substring "brown fox" split similarly on space at position 6 *)

  (* acc for "brown": collected backwards "nwor b" reversed is "brown" actually we collect backwards: 'n', 'w', 'o', 'r', 'b' *)

  (* sort_chars "nwor b" but space is handled separately, so acc = "nwor b" without space is "nwor b" reversed chars are 'n','w','o','r','b' collected backwards so acc is "nwor b"? Wait, acc only collects characters until space, so after space, acc is empty initially and then we have "brown" etc. *)

  (* Actually after first space at position 6, we call anti_shuffle_aux on "brown fox" with acc = EmptyString *)

  (* Process "brown" similarly *)

  (* First space inside "brown fox" is after 'n' *)

  (* acc collecting 'n', 'w', 'o', 'r', 'b' backwards: "nworb" *)

  (* sort_chars "nworb" = sorted characters of "brown" = "bnorw" *)

  (* Then space *)

  (* Then "fox" processed at the end with no space, so sorted "fox" reversed, equals "fox" after sorting *)

  (* Putting all parts together: "Qciku bnorw fox" *)

  reflexivity.
Qed.