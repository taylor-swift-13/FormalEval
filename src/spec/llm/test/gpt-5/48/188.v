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

Example palindrome_long_string_false: is_palindrome_spec "A 12zZ2geeseaea@@@@!3Tacoman, a plan, geesea canal: PanamaTaco not" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - pose proof (string_dec "A 12zZ2geeseaea@@@@!3Tacoman, a plan, geesea canal: PanamaTaco not"
                          (rev_string "A 12zZ2geeseaea@@@@!3Tacoman, a plan, geesea canal: PanamaTaco not")) as Hdec.
    destruct Hdec as [Heq | Hneq].
    + vm_compute in Heq.
      injection Heq as Hch _.
      vm_compute in Hch.
      inversion Hch.
    + exact Hneq.
Qed.