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

Example test_fix_spaces : fix_spaces_spec 
  ("   Ex     2" ++ String (ascii_of_nat 10) ("mple" ++ String (ascii_of_nat 9) "Example   3"))
  ("-Ex-2" ++ String (ascii_of_nat 10) ("mple" ++ String (ascii_of_nat 9) "Example-3")).
Proof.
  unfold fix_spaces_spec.
  
  (* Process first 3 spaces *)
  apply FS_Space_Long with (n := 3).
  { reflexivity. }
  { repeat constructor. }
  simpl.

  (* Process 'E' *)
  apply FS_Char.
  { compute; congruence. }

  (* Process 'x' *)
  apply FS_Char.
  { compute; congruence. }

  (* Process 5 spaces *)
  apply FS_Space_Long with (n := 5).
  { reflexivity. }
  { repeat constructor. }
  simpl.

  (* Process '2' *)
  apply FS_Char.
  { compute; congruence. }

  (* Process Newline *)
  apply FS_Char.
  { compute; congruence. }

  (* Process 'm' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'p' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'l' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'e' *)
  apply FS_Char.
  { compute; congruence. }

  (* Process Tab *)
  apply FS_Char.
  { compute; congruence. }

  (* Process 'E' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'x' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'a' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'm' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'p' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'l' *)
  apply FS_Char.
  { compute; congruence. }
  (* Process 'e' *)
  apply FS_Char.
  { compute; congruence. }

  (* Process last 3 spaces *)
  apply FS_Space_Long with (n := 3).
  { reflexivity. }
  { repeat constructor. }
  simpl.

  (* Process '3' *)
  apply FS_Char.
  { compute; congruence. }

  (* End of string *)
  apply FS_Empty.
Qed.