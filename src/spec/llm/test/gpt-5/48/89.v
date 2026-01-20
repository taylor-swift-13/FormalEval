Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Fixpoint rev_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String a s' => String.append (rev_string s') (String a EmptyString)
  end.

Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  (result = true /\ text = rev_string text) \/
  (result = false /\ text <> rev_string text).

Definition second_char (s : string) : option ascii :=
  match s with
  | String _ (String b _) => Some b
  | _ => None
  end.

Example palindrome_long_string_false: is_palindrome_spec "abcaabcbreWaes it a car rereWas it a car or a cat I saw?feracecaror a ccat I sawreefrer?feraa" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    pose proof (f_equal second_char H) as Hsc.
    simpl in Hsc.
    discriminate Hsc.
Qed.