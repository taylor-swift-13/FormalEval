Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import PeanoNat.
Require Import Lia.
Open Scope string_scope.

(* 表示从 input 的第 i 位开始，与 substr 完全匹配 *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

(* Spec: output是input中substring出现的次数 *)
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

Example test_how_many_times_empty_input_x : problem_18_spec "" "x" 0.
Proof.
  unfold problem_18_spec.
  exists [].
  repeat split.
  - constructor.
  - intros i H_in. inversion H_in.
  - intros i H_len H_match.
    unfold match_at in H_match.
    destruct H_match as [H_len_sub _].
    simpl in H_len_sub. lia.
  - reflexivity.
Qed.