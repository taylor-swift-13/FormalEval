Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition pluck_spec (arr : list Z) (res : list Z) : Prop :=
((forall x, In x arr -> Z.even x = false) /\ res = nil) \/
(exists min_even i,
  Z.even min_even = true /\
  In min_even arr /\
  (forall y, In y arr -> Z.even y = true -> Z.le min_even y) /\
  nth_error arr i = Some min_even /\
  (forall j, Nat.lt j i -> nth_error arr j <> Some min_even) /\
  res = min_even :: Z.of_nat i :: nil).

Example pluck_test : pluck_spec [4; 2; 3] [2; 1].
Proof.
  unfold pluck_spec.
  right.
  (* Instantiate the existential variables: min_even = 2, index = 1 *)
  exists 2, 1%nat.
  (* Use repeat split to break down the conjunctions into individual subgoals *)
  repeat split.
  
  - (* 1. Prove 2 is even *)
    reflexivity.
  
  - (* 2. Prove 2 is in the list *)
    simpl. right. left. reflexivity.
  
  - (* 3. Prove 2 is the minimum even number *)
    intros y H_in H_even.
    simpl in H_in.
    destruct H_in as [H4 | [H2 | [H3 | H_nil]]].
    + (* y = 4 *)
      subst. lia.
    + (* y = 2 *)
      subst. lia.
    + (* y = 3 *)
      subst. simpl in H_even. discriminate.
    + (* End of list *)
      contradiction.

  - (* 4. Prove 2 is at index 1 *)
    reflexivity.

  - (* 5. Prove 2 is the first occurrence (index < 1 implies not 2) *)
    intros j H_lt.
    destruct j.
    + (* j = 0 *)
      simpl. intro H_eq. inversion H_eq.
      (* 4 <> 2, handled by discriminate *)
      discriminate.
    + (* j >= 1 *)
      (* j < 1 implies j = 0, so j >= 1 is a contradiction *)
      lia.

  - (* 6. Prove the result list matches construction *)
    simpl. reflexivity.
Qed.