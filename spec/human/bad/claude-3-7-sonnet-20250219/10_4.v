From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
  forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

Example problem_10_spec_xyx :
  problem_10_spec "xyx" "xyx".
Proof.
  unfold problem_10_spec.
  split.
  - simpl. reflexivity.
  - split.
    + unfold palindrome.
      simpl.
      reflexivity.
    + intros p [Hpref Hpal].
      rewrite <- Hpal.
      (* p = string_of_list_ascii (rev (list_ascii_of_string p)) *)
      (* Since p starts with "xyx", p length >= 3 *)
      (* We want to show length "xyx" <= length p *)
      apply String.length_prefix_le in Hpref.
      assumption.
Qed.