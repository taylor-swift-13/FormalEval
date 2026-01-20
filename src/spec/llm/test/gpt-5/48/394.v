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

Example palindrome_test_case: is_palindrome_spec "A man, a plaWas it sawa car o r a cat I petssaw?n, a erecaisnral,  Panama" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    remember (fun s : string =>
                match s with
                | EmptyString => Ascii.ascii_of_nat 0
                | String c _ => c
                end) as head.
    apply (f_equal head) in H.
    subst head.
    simpl in H.
    discriminate.
Qed.