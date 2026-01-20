Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Local Open Scope string_scope.

Fixpoint drop (n : nat) (s : string) : string :=
  match n, s with
  | 0, _ => s
  | S n', EmptyString => EmptyString
  | S n', String _ s' => drop n' s'
  end.

Fixpoint is_prefixb (t u : string) : bool :=
  match t, u with
  | EmptyString, _ => true
  | String ct rt, String cu ru =>
      if ascii_dec ct cu then is_prefixb rt ru else false
  | String _ _, EmptyString => false
  end.

Definition how_many_times_spec (s substring : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => is_prefixb substring (drop i s))
                                 (List.seq 0 (String.length s))).

Example how_many_times_spec_test_the_quick_brown_fox_jumps_over_the_lazy_dotheg__racecarapenaapapayapineappale :
  how_many_times_spec "The quick brown fox jumps over the lazy dotheg." "racecarapenaapapayapineappale" 0%nat.
Proof.
  unfold how_many_times_spec.
  vm_compute.
  reflexivity.
Qed.

Example how_many_times_spec_test_the_quick_brown_fox_jumps_over_the_lazy_dotheg__racecarapenaapapayapineappale_Z :
  exists res : nat, how_many_times_spec "The quick brown fox jumps over the lazy dotheg." "racecarapenaapapayapineappale" res /\ Z.of_nat res = 0%Z.
Proof.
  exists 0%nat.
  split.
  - apply how_many_times_spec_test_the_quick_brown_fox_jumps_over_the_lazy_dotheg__racecarapenaapapayapineappale.
  - simpl. reflexivity.
Qed.