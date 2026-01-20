Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.

Open Scope string_scope.

Fixpoint count_consecutive_spaces (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => 
      if Ascii.ascii_dec c " " then S (count_consecutive_spaces rest) else 0
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
    count_consecutive_spaces (String " " s) <= 2 ->
    fix_spaces_rel s s_out ->
    fix_spaces_rel (String " " s) (String "_" s_out)
| FS_Space_Long : forall s s_out n,
    count_consecutive_spaces (String " " s) = n ->
    n > 2 ->
    fix_spaces_rel (skip_n n (String " " s)) s_out ->
    fix_spaces_rel (String " " s) (String "-" s_out).

Definition fix_spaces_spec (text : string) (ans : string) : Prop :=
  fix_spaces_rel text ans.

Lemma char_neq_space_E : ("E"%char <> " "%char).
Proof.
  intro H. discriminate H.
Qed.

Lemma char_neq_space_x : ("x"%char <> " "%char).
Proof.
  intro H. discriminate H.
Qed.

Lemma char_neq_space_a : ("a"%char <> " "%char).
Proof.
  intro H. discriminate H.
Qed.

Lemma char_neq_space_m : ("m"%char <> " "%char).
Proof.
  intro H. discriminate H.
Qed.

Lemma char_neq_space_p : ("p"%char <> " "%char).
Proof.
  intro H. discriminate H.
Qed.

Lemma char_neq_space_l : ("l"%char <> " "%char).
Proof.
  intro H. discriminate H.
Qed.

Lemma char_neq_space_e : ("e"%char <> " "%char).
Proof.
  intro H. discriminate H.
Qed.

Example test_example : fix_spaces_spec "Example" "Example".
Proof.
  unfold fix_spaces_spec.
  apply FS_Char. exact char_neq_space_E.
  apply FS_Char. exact char_neq_space_x.
  apply FS_Char. exact char_neq_space_a.
  apply FS_Char. exact char_neq_space_m.
  apply FS_Char. exact char_neq_space_p.
  apply FS_Char. exact char_neq_space_l.
  apply FS_Char. exact char_neq_space_e.
  apply FS_Empty.
Qed.