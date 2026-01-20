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

Example palindrome_test_case: is_palindrome_spec "Step12zZ2psaw?12@zZ2@@@@!3j  nama21ets@@@@!3j  12zZ2it@@2A man., wsaAeNAa plan, Pa  Pana.ma.Zz21" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. intro H. discriminate H.
Qed.