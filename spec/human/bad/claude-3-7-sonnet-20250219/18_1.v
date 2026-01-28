Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Open Scope string_scope.

(* 表示从 input 的第 i 位开始，与 substr 完全匹配 *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (forall i, In i indices -> match_at i input substring) /\
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    output = List.length indices.

Example test_empty_and_x_0 :
  problem_18_spec "" "x" 0.
Proof.
  unfold problem_18_spec.
  exists [].
  split.
  - apply NoDup_nil.
  split.
  - intros i H_in. inversion H_in.
  split.
  - intros i Hbound Hmatch.
    unfold match_at in Hmatch.
    destruct Hmatch as [Hlen [Hbound2 _]].
    (* length input = 0, length substring = 1, so i + 1 ≤ 0 impossible *)
    lia.
  - reflexivity.
Qed.