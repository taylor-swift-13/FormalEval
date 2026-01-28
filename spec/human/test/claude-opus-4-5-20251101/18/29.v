Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import Lia.
Open Scope string_scope.

Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

Definition problem_18_pre (input substring : string) : Prop := True.

Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (forall i, In i indices -> match_at i input substring) /\
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    output = List.length indices.

Example test_problem_18 : problem_18_spec "ababa" "ababa" 1.
Proof.
  unfold problem_18_spec.
  exists [0].
  split.
  - constructor.
    + intro H. inversion H.
    + constructor.
  - split.
    + intros i H.
      destruct H as [H | H].
      * subst i.
        unfold match_at.
        split.
        -- simpl. lia.
        -- split.
           ++ simpl. lia.
           ++ intros j Hj.
              simpl in Hj.
              destruct j as [|[|[|[|[|j']]]]]; simpl; try reflexivity; lia.
      * inversion H.
    + split.
      * intros i Hlen Hmatch.
        unfold match_at in Hmatch.
        destruct Hmatch as [Hsublen [Hbound Hget]].
        simpl in Hsublen.
        simpl in Hbound.
        simpl in Hlen.
        assert (i = 0) by lia.
        subst i.
        left. reflexivity.
      * reflexivity.
Qed.