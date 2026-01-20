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

Example palindrome_aabca_false: is_palindrome_spec "aabca" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. intros H.
    pose proof (f_equal (fun s => match s with String _ (String c _) => c | _ => Ascii false false false false false false false false end) H) as Hc.
    simpl in Hc.
    inversion Hc.
Qed.