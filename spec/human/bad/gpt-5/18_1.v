Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import Lia.
Require Import ZArith.
Open Scope string_scope.
Open Scope nat_scope.

(* 表示从 input 的第 i 位开始，与 substr 完全匹配 *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0%nat /\
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

Example problem_18_example_0 : problem_18_spec "" "x" 0%nat.
Proof.
  unfold problem_18_spec.
  exists [].
  split.
  - apply NoDup_nil.
  split.
  - intros i HIn. inversion HIn.
  split.
  - intros i HiLen Hmatch.
    exfalso.
    simpl in HiLen.
    lia.
  - simpl. reflexivity.
Qed.

Example problem_18_example_Z :
  exists o, problem_18_spec "" "x" o /\ Z.of_nat o = 0%Z.
Proof.
  exists 0%nat.
  split.
  - apply problem_18_example_0.
  - reflexivity.
Qed.