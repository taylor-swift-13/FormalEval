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

Example test_problem_18 : problem_18_spec "ababa" "aba" 2.
Proof.
  unfold problem_18_spec.
  exists [0; 2].
  split.
  - constructor.
    + simpl. intros [H | H]; discriminate.
    + constructor.
      * simpl. intros [].
      * constructor.
  - split.
    + intros i H.
      unfold match_at.
      simpl in H.
      destruct H as [H | [H | H]].
      * subst i. simpl. split. lia. split. lia.
        intros j Hj. simpl in Hj.
        destruct j as [|[|[|]]]; try lia; reflexivity.
      * subst i. simpl. split. lia. split. lia.
        intros j Hj. simpl in Hj.
        destruct j as [|[|[|]]]; try lia; reflexivity.
      * contradiction.
    + split.
      * intros i Hlen Hmatch.
        unfold match_at in Hmatch.
        destruct Hmatch as [Hsublen [Hbound Hget]].
        simpl in Hsublen, Hbound, Hlen.
        assert (i <= 2) by lia.
        destruct i as [|[|[|]]]; try lia.
        -- left. reflexivity.
        -- right. 
           specialize (Hget 0).
           simpl in Hget.
           assert (H0: 0 < 3) by lia.
           specialize (Hget H0).
           discriminate.
        -- right. left. reflexivity.
      * reflexivity.
Qed.