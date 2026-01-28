Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example problem_29_test_case : problem_29_spec ["a"; "ab"; "abc"; "ba"; "bb"; "bc"] "a" ["a"; "ab"; "abc"].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - intros s; split.
    + intros Hin. split.
      * destruct Hin as [Hs | Hin1].
        { subst s. simpl. left. reflexivity. }
        { destruct Hin1 as [Hs1 | Hin2].
          { subst s. simpl. right. left. reflexivity. }
          { destruct Hin2 as [Hs2 | HinNil].
            { subst s. simpl. right. right. left. reflexivity. }
            { inversion HinNil. } } }
      * destruct Hin as [Hs | Hin1].
        { subst s. simpl. reflexivity. }
        { destruct Hin1 as [Hs1 | Hin2].
          { subst s. simpl. reflexivity. }
          { destruct Hin2 as [Hs2 | HinNil].
            { subst s. simpl. reflexivity. }
            { inversion HinNil. } } }
    + intros [Hin Hpref].
      destruct Hin as [Hs | Hin1].
      * subst s. simpl. left. reflexivity.
      * destruct Hin1 as [Hs1 | Hin2].
        { subst s. simpl. right. left. reflexivity. }
        { destruct Hin2 as [Hs2 | Hin3].
          { subst s. simpl. right. right. left. reflexivity. }
          { destruct Hin3 as [Hs3 | Hin4].
            { subst s. simpl in Hpref. discriminate Hpref. }
            { destruct Hin4 as [Hs4 | Hin5].
              { subst s. simpl in Hpref. discriminate Hpref. }
              { destruct Hin5 as [Hs5 | HinNil].
                { subst s. simpl in Hpref. discriminate Hpref. }
                { inversion HinNil. } } } } }
Qed.