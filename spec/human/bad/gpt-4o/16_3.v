Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope nat_scope.
Open Scope string_scope.

Definition is_upper (a: ascii) : bool :=
  let n := nat_of_ascii a in
  (65 <=? n)%nat && (n <=? 90)%nat.

Definition lower (a: ascii) : ascii :=
  if is_upper a then
    ascii_of_nat (nat_of_ascii a + 32)
  else a.

Definition problem_16_spec (s: string) (output: nat) : Prop :=
  exists D: list ascii,
    NoDup D /\
    (forall i, i < String.length s -> 
      match String.get i s with
      | Some c => In (lower c) D
      | None => False
      end) /\
    (forall d, In d D -> exists i, i < String.length s /\ 
      match String.get i s with
      | Some c => d = lower c
      | None => False
      end) /\
    output = List.length D.

Example example_0 :
  problem_16_spec "abcdecadeCADE" 5.
Proof.
  unfold problem_16_spec.
  exists [lower "a"%char; lower "b"%char; lower "c"%char; lower "d"%char; lower "e"%char].
  split.
  - apply NoDup_cons; [simpl; auto |].
    apply NoDup_cons; [simpl; auto |].
    apply NoDup_cons; [simpl; auto |].
    apply NoDup_cons; [simpl; auto |].
    apply NoDup_cons; [simpl; auto | apply NoDup_nil].
  - split.
    + intros i Hi. 
      destruct (String.get i "abcdecadeCADE") eqn:Heq.
      * simpl. destruct c; simpl; repeat (try apply in_cons; try apply in_eq).
      * simpl in Hi. rewrite Heq in Hi. contradiction.
    + split.
      * intros d Hin. 
        destruct Hin as [Hin | [Hin | [Hin | [Hin | [Hin | Hin]]]]]; subst d;
        repeat match goal with
        | |- exists i, _ => exists (String.index "abcdecadeCADE" (ascii_of_nat (nat_of_ascii d)))
        end; split; try auto; simpl; rewrite String.index_correct; auto.
      * reflexivity.
Qed.