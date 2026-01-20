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

Lemma rev_string_append_last: forall s a,
  rev_string (String.append s (String a EmptyString)) = String a (rev_string s).
Proof.
  induction s; simpl; intros; [reflexivity | rewrite IHs; reflexivity].
Qed.

Definition long_prefix : string :=
"Step12zZ2pets@@@@!3j  12zZ2it@@2A man., Step12zZ2pets@@@@!3j  12zZ2it@@2A man., a plan, Pa  Pana.ma.Zz21wsaAeNAa plan, Pa  Pana.ma.ZEvil is a A maPa canalo, Pana,mano @canal12zZ2@@Aorcatgees,PanplanfofoemaIn,StepeIaem,noan,,Elba.amae@@!2j3jd3!@@@2Zz21, Pana.ma.name of a fvIoeman,s as I live.z2".

Example palindrome_long_false:
  is_palindrome_spec
    (String.append long_prefix "1")
    false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    rewrite (rev_string_append_last long_prefix "1"%char) in H.
    remember long_prefix as p eqn:Hp.
    destruct p as [|a' p'].
    + simpl in H. discriminate Hp.
    + simpl in H. inversion Hp; subst a' p'. discriminate H.
Qed.