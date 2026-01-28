Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import Lia.
Open Scope string_scope.

(* 表示从 input 的第 i 位开始，与 substr 完全匹配 *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

(* Spec: output是input中substring出现的次数 *)
(* Pre: no additional constraints for `how_many_times` by default *)
Definition problem_18_pre (input substring : string) : Prop := True.

Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (* indices中所有位置都匹配 *)
    (forall i, In i indices -> match_at i input substring) /\
    (* 所有匹配位置都在indices中 *)
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    (* output是匹配次数 *)
    output = List.length indices.

Example test_problem_18 : problem_18_spec "john doe" "john" 1.
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
              destruct j as [| [| [| [|]]]]; try lia; reflexivity.
      * inversion H.
    + split.
      * intros i Hlen Hmatch.
        unfold match_at in Hmatch.
        destruct Hmatch as [Hsublen [Hbound Hget]].
        simpl in Hsublen.
        simpl in Hbound.
        simpl in Hlen.
        assert (i <= 4) by lia.
        destruct i as [| [| [| [| [|]]]]]; try lia.
        -- left. reflexivity.
        -- specialize (Hget 0). simpl in Hget. 
           assert (0 < 4) by lia. specialize (Hget H0).
           discriminate Hget.
        -- specialize (Hget 0). simpl in Hget.
           assert (0 < 4) by lia. specialize (Hget H0).
           discriminate Hget.
        -- specialize (Hget 0). simpl in Hget.
           assert (0 < 4) by lia. specialize (Hget H0).
           discriminate Hget.
        -- specialize (Hget 0). simpl in Hget.
           assert (0 < 4) by lia. specialize (Hget H0).
           discriminate Hget.
      * reflexivity.
Qed.