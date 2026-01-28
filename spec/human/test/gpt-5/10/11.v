From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

Fixpoint prefix (a b : string) : bool :=
  match a, b with
  | EmptyString, _ => true
  | String a1 a2, String b1 b2 =>
      if Ascii.eqb a1 b1 then prefix a2 b2 else false
  | _, _ => false
  end.

Definition problem_10_pre : Prop := True.

Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
  forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

Lemma prefix_length_le : forall a b, prefix a b = true -> String.length a <= String.length b.
Proof.
  induction a as [|a1 a2 IHa]; intros b H; simpl in *.
  - lia.
  - destruct b as [| b1 b2].
    + simpl in H. discriminate.
    + simpl in H. destruct (Ascii.eqb a1 b1) eqn:E.
      * apply IHa in H. simpl. lia.
      * discriminate.
Qed.

Example problem_10_test_case_refer :
  problem_10_spec "refer" "refer".
Proof.
  unfold problem_10_spec.
  split.
  - simpl. reflexivity.
  - split.
    + unfold palindrome. simpl. reflexivity.
    + intros p [Hpref Hpal].
      apply prefix_length_le in Hpref.
      simpl. exact Hpref.
Qed.