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

Example test_fix_spaces_example : fix_spaces_spec "  spaces  eveThis is  a This This is  a This is  a  tes test  spaceNoSpacesHello r   WorldHere is  a  tes testry  where  " "__spaces__eveThis_is__a_This_This_is__a_This_is__a__tes_test__spaceNoSpacesHello_r-WorldHere_is__a__tes_testry__where__".
Proof.
  unfold fix_spaces_spec.
  Ltac solve_step :=
    match goal with
    | [ |- fix_spaces_rel EmptyString EmptyString ] => apply FS_Empty
    | [ |- fix_spaces_rel (String ?c ?s) _ ] =>
        let is_space := eval compute in (if Ascii.ascii_dec c " "%char then true else false) in
        match is_space with
        | true => 
             let n := eval compute in (count_consecutive_spaces (String c s)) in
             match n with
             | 0 => fail "Impossible"
             | 1 => apply FS_Space_Short; [ simpl; repeat constructor | ]
             | 2 => apply FS_Space_Short; [ simpl; repeat constructor | ]
             | _ => eapply FS_Space_Long; [ reflexivity | repeat constructor | simpl ]
             end
        | false => apply FS_Char; [ discriminate | ]
        end
    end.
  repeat solve_step.
Qed.