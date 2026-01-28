From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

Definition palindrome (s : string) : Prop :=
  string_of_list_ascii (List.rev (list_ascii_of_string s)) = s.

Fixpoint prefix (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, _ => true
  | String a s1', String b s2' =>
      if Ascii.eqb a b then prefix s1' s2' else false
  | _, _ => false
  end.

Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
  forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

Lemma prefix_empty : forall s, prefix EmptyString s = true.
Proof.
  intros s. simpl. reflexivity.
Qed.

Lemma palindrome_empty : palindrome EmptyString.
Proof.
  unfold palindrome.
  simpl. reflexivity.
Qed.

Lemma length_empty : String.length EmptyString = 0.
Proof. reflexivity. Qed.

Lemma prefix_implies_length : forall s1 s2,
  prefix s1 s2 = true -> String.length s1 <= String.length s2.
Proof.
  intros s1. induction s1; intros s2 H.
  - simpl. lia.
  - destruct s2; try discriminate.
    simpl in H. destruct (Ascii.eqb a a0) eqn:Heq; try discriminate.
    apply IHs1 in H. simpl. lia.
Qed.

Lemma empty_prefix_only_empty_palindrome : forall p,
  prefix EmptyString p = true -> palindrome p -> String.length EmptyString <= String.length p.
Proof.
  intros p Hprefix Hpal.
  simpl. lia.
Qed.

Example test_empty_string : problem_10_spec "" "".
Proof.
  unfold problem_10_spec.
  split. 
  - apply prefix_empty.
  - split.
    + apply palindrome_empty.
    + intros p [Hprefix Hpalindrome].
      simpl. lia.
Qed.