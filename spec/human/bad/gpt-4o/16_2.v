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

Example example_1 :
  problem_16_spec "abcde" 5.
Proof.
  unfold problem_16_spec.
  exists (map lower (list_ascii_of_string "abcde")).
  split.
  - apply NoDup_map_injective.
    + unfold lower. intros. destruct (is_upper x) eqn:Hx, (is_upper y) eqn:Hy.
      * apply nat_of_ascii_inj. rewrite <- (ascii_nat_embedding x), <- (ascii_nat_embedding y). 
        rewrite H. reflexivity.
      * apply nat_of_ascii_inj. rewrite <- (ascii_nat_embedding x), <- (ascii_nat_embedding y). 
        rewrite H. reflexivity.
      * apply nat_of_ascii_inj. rewrite <- (ascii_nat_embedding x), <- (ascii_nat_embedding y). 
        rewrite H. reflexivity.
      * apply nat_of_ascii_inj. rewrite <- (ascii_nat_embedding x), <- (ascii_nat_embedding y). 
        rewrite H. reflexivity.
    + apply NoDup_list_ascii_of_string.
  - split.
    + intros i Hi. simpl.
      apply in_map.
      apply list_ascii_of_string_get_in. assumption.
    + split.
      * intros d Hd. apply in_map_iff in Hd. destruct Hd as [c [Hc Hin]].
        exists (index_of c (list_ascii_of_string "abcde")).
        split.
        -- apply list_ascii_of_string_index_of_lt. assumption.
        -- unfold lower. rewrite Hc. reflexivity.
      * rewrite map_length. apply list_ascii_of_string_length.
Qed.