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

Example problem_29_test_case : problem_29_spec ["world"; "heworldlo"; "house"] "h" ["heworldlo"; "house"].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - intros s; split.
    + intros Hin.
      destruct Hin as [Hin0 | Hinrest].
      * subst s. split.
        { right. left. reflexivity. }
        { simpl. reflexivity. }
      * destruct Hinrest as [Hin1 | HinNil].
        { subst s. split.
          { right. right. left. reflexivity. }
          { simpl. reflexivity. } }
        { inversion HinNil. }
    + intros [Hin Hpref].
      destruct Hin as [Hin0 | Hinrest].
      * subst s. exfalso. simpl in Hpref. discriminate Hpref.
      * destruct Hinrest as [Hin1 | Hinrest'].
        { subst s. left. reflexivity. }
        { destruct Hinrest' as [Hin2 | HinNil].
          { subst s. right. left. reflexivity. }
          { inversion HinNil. } }
Qed.