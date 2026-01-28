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

Example problem_29_test_case : problem_29_spec ["apple"; "banana"; "orange"; "apricot"; "kiwi"] "ap" ["apple"; "apricot"].
Proof.
  unfold problem_29_spec.
  split.
  - eapply sub_cons_match.
    eapply sub_cons_skip.
    eapply sub_cons_skip.
    eapply sub_cons_match.
    apply sub_nil.
  - intros s; split.
    + intros H.
      destruct H as [Happle | Hrest].
      * subst s. split.
        { left. reflexivity. }
        { simpl. reflexivity. }
      * destruct Hrest as [Hapricot | Hnil].
        { subst s. split.
          { right. right. right. left. reflexivity. }
          { simpl. reflexivity. }
        }
        { inversion Hnil. }
    + intros [Hin Hpref].
      destruct Hin as [Happle | Hin_rest].
      * subst s. left. reflexivity.
      * destruct Hin_rest as [Hbanana | Hin_rest2].
        { subst s. exfalso. simpl in Hpref. discriminate Hpref. }
        { destruct Hin_rest2 as [Horange | Hin_rest3].
          { subst s. exfalso. simpl in Hpref. discriminate Hpref. }
          { destruct Hin_rest3 as [Hapricot | Hin_rest4].
            { subst s. right. left. reflexivity. }
            { destruct Hin_rest4 as [Hkiwi | Hin_nil].
              { subst s. exfalso. simpl in Hpref. discriminate Hpref. }
              { inversion Hin_nil. }
            }
          }
        }
Qed.