Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.

Open Scope string_scope.

(* Specification Definitions *)

Fixpoint count_consecutive_spaces (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => 
      if Ascii.ascii_dec c " "%char then S (count_consecutive_spaces rest) else 0
  end.

Fixpoint skip_n (n : nat) (s : string) : string :=
  match n with
  | 0 => s
  | S n' => 
      match s with
      | EmptyString => EmptyString
      | String _ rest => skip_n n' rest
      end
  end.

Inductive fix_spaces_rel : string -> string -> Prop :=
| FS_Empty : fix_spaces_rel EmptyString EmptyString
| FS_Char : forall c s s_out,
    c <> " "%char ->
    fix_spaces_rel s s_out ->
    fix_spaces_rel (String c s) (String c s_out)
| FS_Space_Short : forall s s_out,
    count_consecutive_spaces (String " "%char s) <= 2 ->
    fix_spaces_rel s s_out ->
    fix_spaces_rel (String " "%char s) (String "_" s_out)
| FS_Space_Long : forall s s_out n,
    count_consecutive_spaces (String " "%char s) = n ->
    n > 2 ->
    fix_spaces_rel (skip_n n (String " "%char s)) s_out ->
    fix_spaces_rel (String " "%char s) (String "-" s_out).

Definition fix_spaces_spec (text : string) (ans : string) : Prop :=
  fix_spaces_rel text ans.

(* Test Case Proof *)

Example test_fix_spaces_complex : fix_spaces_spec "    Example   2    Example words  2" "-Example-2-Example_words__2".
Proof.
  unfold fix_spaces_spec.
  
  (* Segment 1: "    " (4 spaces) -> "-" *)
  eapply FS_Space_Long.
  { reflexivity. } (* count = 4 *)
  { repeat constructor. } (* 4 > 2 *)
  simpl.

  (* Segment 2: "Example" *)
  repeat (apply FS_Char; [ discriminate | ]).

  (* Segment 3: "   " (3 spaces) -> "-" *)
  eapply FS_Space_Long.
  { reflexivity. } (* count = 3 *)
  { repeat constructor. } (* 3 > 2 *)
  simpl.

  (* Segment 4: "2" *)
  repeat (apply FS_Char; [ discriminate | ]).

  (* Segment 5: "    " (4 spaces) -> "-" *)
  eapply FS_Space_Long.
  { reflexivity. } (* count = 4 *)
  { repeat constructor. } (* 4 > 2 *)
  simpl.

  (* Segment 6: "Example" *)
  repeat (apply FS_Char; [ discriminate | ]).

  (* Segment 7: " " (1 space) -> "_" *)
  apply FS_Space_Short.
  { simpl. repeat constructor. } (* 1 <= 2 *)
  
  (* Segment 8: "words" *)
  repeat (apply FS_Char; [ discriminate | ]).

  (* Segment 9: "  " (2 spaces) -> "__" *)
  (* First space *)
  apply FS_Space_Short.
  { simpl. repeat constructor. } (* 2 <= 2 *)
  (* Second space *)
  apply FS_Space_Short.
  { simpl. repeat constructor. } (* 1 <= 2 *)

  (* Segment 10: "2" *)
  repeat (apply FS_Char; [ discriminate | ]).

  (* End *)
  apply FS_Empty.
Qed.