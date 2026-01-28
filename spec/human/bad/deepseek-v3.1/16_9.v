Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
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

Definition problem_16_pre (s : string) : Prop := True.

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

Lemma test_case_hello123 : problem_16_spec "hello123" 7.
Proof.
  unfold problem_16_spec.
  exists (map lower (String.to_list "hello123")).
  split.
  - apply NoDup_map_injective.
    + intros x y H.
      unfold lower.
      destruct (is_upper x) eqn:Hu, (is_upper y) eqn:Hu'.
      * apply ascii_of_nat_injective in Hu, Hu'. congruence.
      * intros H0; subst; simpl; apply ascii_of_nat_injective in Hu; congruence.
      * intros H0; subst; simpl; apply ascii_of_nat_injective in Hu; congruence.
      * discriminate.
  - split.
    + intros i H.
      simpl in H.
      destruct (String.get i (String.of_list (map ascii_of_nat (List.map nat_of_ascii (map ascii_of_nat (String.to_list "hello123")))))) as [c|] eqn:Hget.
      * rewrite String.get_eq in Hget; [|auto]. subst.
        rewrite String.of_list_length.
        rewrite List.length_map.
        simpl.
        rewrite List.map_length.
        reflexivity.
      * inversion H.
    + split.
      * intros d H.
        simpl in H.
        destruct (In_map_lower_dec d (String.to_list "hello123")) as [HIn | HNotIn].
        -- destruct HIn as [i [Hi Hc]].
           exists i.
           split; [lia|].
           rewrite String.get_eq; auto.
        -- contradiction.
      * reflexivity.
Qed.