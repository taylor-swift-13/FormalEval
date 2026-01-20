Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Fixpoint factorial (k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => (S k') * factorial k'
  end.

Fixpoint sum_1_to_i (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => i + sum_1_to_i i'
  end.

Definition f_spec (n : nat) (l : list nat) : Prop :=
  length l = n /\
  (forall i, 1 <= i <= n ->
    nth (i-1) l 0 = 
      if Nat.even i then factorial i else sum_1_to_i i).

Example test_case : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  split.
  - (* Proof of length condition *)
    simpl. reflexivity.
  - (* Proof of element values condition *)
    intros i H_bounds.
    (* Since 1 <= i <= 5, we enumerate the possible values of i *)
    assert (H_cases: i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
    destruct H_cases as [H1 | [H2 | [H3 | [H4 | H5]]]]; subst i.
    + (* i = 1 *)
      simpl. reflexivity.
    + (* i = 2 *)
      simpl. reflexivity.
    + (* i = 3 *)
      simpl. reflexivity.
    + (* i = 4 *)
      simpl. reflexivity.
    + (* i = 5 *)
      simpl. reflexivity.
Qed.