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

Example test_fix_spaces_complex : fix_spaces_spec 
  "    his     A-B-*_-E-C   Ex     2
mple	Example  m 3thitssxa3eis    EExample-C   "
  "-his-A-B-*_-E-C-Ex-2
mple	Example__m_3thitssxa3eis-EExample-C-".
Proof.
  unfold fix_spaces_spec.
  
  (* 4 spaces *)
  eapply FS_Space_Long.
  { reflexivity. }
  { repeat constructor. }
  
  (* his *)
  repeat (apply FS_Char; [ discriminate | ]).
  
  (* 5 spaces *)
  eapply FS_Space_Long.
  { reflexivity. }
  { repeat constructor. }
  
  (* A-B-*_-E-C *)
  repeat (apply FS_Char; [ discriminate | ]).
  
  (* 3 spaces *)
  eapply FS_Space_Long.
  { reflexivity. }
  { repeat constructor. }
  
  (* Ex *)
  repeat (apply FS_Char; [ discriminate | ]).
  
  (* 5 spaces *)
  eapply FS_Space_Long.
  { reflexivity. }
  { repeat constructor. }
  
  (* 2\nmple\tExample *)
  repeat (apply FS_Char; [ discriminate | ]).
  
  (* 2 spaces "  m" *)
  apply FS_Space_Short.
  { simpl. repeat constructor. }
  apply FS_Space_Short.
  { simpl. repeat constructor. }
  
  (* m *)
  apply FS_Char. { discriminate. }
  
  (* 1 space " " *)
  apply FS_Space_Short.
  { simpl. repeat constructor. }
  
  (* 3thitssxa3eis *)
  repeat (apply FS_Char; [ discriminate | ]).
  
  (* 4 spaces *)
  eapply FS_Space_Long.
  { reflexivity. }
  { repeat constructor. }
  
  (* EExample-C *)
  repeat (apply FS_Char; [ discriminate | ]).
  
  (* 3 spaces *)
  eapply FS_Space_Long.
  { reflexivity. }
  { repeat constructor. }
  
  apply FS_Empty.
Qed.