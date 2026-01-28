Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.
Import ListNotations.
Import Nat.

Inductive count_ones_helper_rel : nat -> nat -> nat -> Prop :=
| cohr_zero_fuel : forall n, count_ones_helper_rel n 0 0
| cohr_zero_n : forall fuel, count_ones_helper_rel 0 fuel 0
| cohr_step : forall n fuel fuel' ones_tail,
    fuel = S fuel' ->
    n <> 0 ->
    count_ones_helper_rel (n / 2) fuel' ones_tail ->
    count_ones_helper_rel n fuel ((n mod 2) + ones_tail).

Inductive count_ones_rel : nat -> nat -> Prop :=
| cor_base : forall n ones, count_ones_helper_rel n n ones -> count_ones_rel n ones.

Definition lt_custom (a b : nat) : Prop :=
  exists ones_a ones_b,
    count_ones_rel a ones_a /\
    count_ones_rel b ones_b /\
    ((ones_a < ones_b) \/ (ones_a = ones_b /\ a < b)).

Definition lt_custom_bool (a b : nat) : Prop :=
  exists ones_a ones_b,
    count_ones_rel a ones_a /\
    count_ones_rel b ones_b /\
    ((ones_a <? ones_b) = true \/ ((ones_a =? ones_b) = true /\ (a <? b) = true)).

Inductive insert_sorted_rel : nat -> list nat -> list nat -> Prop :=
  | isr_nil : forall x, insert_sorted_rel x [] [x]
  | isr_insert : forall x h t,
      lt_custom_bool x h ->
      insert_sorted_rel x (h :: t) (x :: h :: t)
  | isr_skip : forall x h t result,
      ~ lt_custom_bool x h ->
      insert_sorted_rel x t result ->
      insert_sorted_rel x (h :: t) (h :: result).

Inductive sort_array_impl_rel : list nat -> list nat -> Prop :=
| sair_nil : sort_array_impl_rel [] []
| sair_cons : forall h t sorted_tail result,
    sort_array_impl_rel t sorted_tail ->
    insert_sorted_rel h sorted_tail result ->
    sort_array_impl_rel (h :: t) result.

Definition problem_116_pre (input : list nat) : Prop := True.

Definition problem_116_spec (input output : list nat) : Prop :=
  sort_array_impl_rel input output.

(* Tactics to automate the proof steps *)

(* Proves count_ones_rel n k for concrete n and k *)
Ltac prove_count :=
  apply cor_base;
  repeat (eapply cohr_step; [ reflexivity | discriminate | ]);
  first [ apply cohr_zero_fuel | apply cohr_zero_n ];
  simpl; reflexivity.

(* Proves lt_custom_bool x y is True with given counts c1 c2 *)
Ltac solve_lt_true c1 c2 :=
  exists c1, c2;
  split; [ prove_count |
    split; [ prove_count |
      simpl; auto ] ].

(* Proves ~ lt_custom_bool x y is True by contradiction *)
Ltac solve_lt_false :=
  let H := fresh "H" in
  intro H;
  destruct H as [? [? [HcA [HcB Hbool]]]];
  inversion HcA; subst; clear HcA;
  repeat match goal with
  | [ h : count_ones_helper_rel _ _ _ |- _ ] => inversion h; subst; clear h
  end;
  inversion HcB; subst; clear HcB;
  repeat match goal with
  | [ h : count_ones_helper_rel _ _ _ |- _ ] => inversion h; subst; clear h
  end;
  simpl in Hbool;
  destruct Hbool as [Hcontra | [Hcontra1 Hcontra2]]; try discriminate.

Example test_problem_116 : problem_116_spec [1; 5; 2; 3; 4] [1; 2; 4; 3; 5].
Proof.
  unfold problem_116_spec.
  
  (* Step 1: Decompose the sort structure *)
  apply sair_cons. (* Process 1 *)
  apply sair_cons. (* Process 5 *)
  apply sair_cons. (* Process 2 *)
  apply sair_cons. (* Process 3 *)
  apply sair_cons. (* Process 4 *)
  apply sair_nil.  (* Base case [] *)

  (* Step 2: Insert 4 into [] -> [4] *)
  apply isr_nil.

  (* Step 3: Insert 3 into [4] *)
  (* 3 (ones: 2) vs 4 (ones: 1). 3 < 4 is false. Skip. *)
  apply isr_skip.
  - solve_lt_false.
  - apply isr_nil.

  (* Step 4: Insert 2 into [4; 3] *)
  (* 2 (ones: 1) vs 4 (ones: 1). 2 < 4 value is true. Insert. *)
  apply isr_insert.
  - solve_lt_true 1 1.

  (* Step 5: Insert 5 into [2; 4; 3] *)
  (* 5 (ones: 2) vs 2 (ones: 1). False. Skip. *)
  apply isr_skip.
  - solve_lt_false.
  (* 5 (ones: 2) vs 4 (ones: 1). False. Skip. *)
  - apply isr_skip.
    + solve_lt_false.
    (* 5 (ones: 2) vs 3 (ones: 2). 5 < 3 value is false. Skip. *)
    + apply isr_skip.
      * solve_lt_false.
      * apply isr_nil.

  (* Step 6: Insert 1 into [2; 4; 3; 5] *)
  (* 1 (ones: 1) vs 2 (ones: 1). 1 < 2 value is true. Insert. *)
  apply isr_insert.
  - solve_lt_true 1 1.
Qed.