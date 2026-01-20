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

Example palindrome_rats_live_on_no_rvil: is_palindrome_spec "Rats live on no rvil" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    apply (f_equal (fun s => match s with | EmptyString => Ascii.ascii_of_nat 0 | String c _ => c end)) in H.
    simpl in H.
    inversion H.
Qed.