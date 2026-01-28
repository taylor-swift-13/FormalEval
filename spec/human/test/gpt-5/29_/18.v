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

Example problem_29_test_case : problem_29_spec ["apple"; "banana"; "orange"; "apricot"; "kiwi"] "a" ["apple"; "apricot"].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_nil.
  - intros s; split.
    + intros Hin.
      destruct Hin as [H | Hin'].
      * subst s.
        split.
        { simpl. left. reflexivity. }
        { simpl. reflexivity. }
      * destruct Hin' as [H | Hin''].
        { subst s.
          split.
          { simpl. right. right. right. left. reflexivity. }
          { simpl. reflexivity. } }
        { inversion Hin''. }
    + intros [Hin Hpref].
      destruct Hin as [H | Hin].
      * subst s. simpl. left. reflexivity.
      * destruct Hin as [H | Hin].
        { subst s. simpl in Hpref. discriminate Hpref. }
        { destruct Hin as [H | Hin].
          { subst s. simpl in Hpref. discriminate Hpref. }
          { destruct Hin as [H | Hin].
            { subst s. simpl. right. left. reflexivity. }
            { destruct Hin as [H | Hin].
              { subst s. simpl in Hpref. discriminate Hpref. }
              { inversion Hin. } } } }
Qed.