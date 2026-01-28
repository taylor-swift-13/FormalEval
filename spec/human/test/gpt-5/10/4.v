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

Example problem_10_test_case_xyx :
  problem_10_spec "xyx" "xyx".
Proof.
  unfold problem_10_spec.
  split.
  - unfold prefix. simpl. reflexivity.
  - split.
    + unfold palindrome. simpl. reflexivity.
    + intros p [Hpref Hpal].
      assert (forall a b, prefix a b = true -> String.length a <= String.length b) as prefix_len.
      { induction a as [|a1 a2 IHa].
        - intros b Hb. simpl. lia.
        - intros [| b1 b2] Hb.
          + simpl in Hb. discriminate.
          + simpl in Hb. destruct (Ascii.eqb a1 b1) eqn:E.
            * apply IHa in Hb. simpl. lia.
            * discriminate.
      }
      specialize (prefix_len "xyx" p Hpref).
      exact prefix_len.
Qed.