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

Example palindrome_hpetsecaisnral_122zZ2: is_palindrome_spec "hpetsecaisnral,122zZ2" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    simpl in H.
    pose proof (f_equal (fun s => match s with | String a _ => a | EmptyString => "x"%char end) H) as Hhead.
    simpl in Hhead.
    pose proof (f_equal Ascii.nat_of_ascii Hhead) as Hn.
    simpl in Hn.
    discriminate.
Qed.