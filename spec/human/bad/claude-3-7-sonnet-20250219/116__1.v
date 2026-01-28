Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Same definitions as given *)

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

(* Fix for count_ones: use well-founded recursion to avoid error *)

Require Import Coq.Wellfounded.Wellfounded.

Fixpoint count_ones_fuel (fuel n : nat) {struct fuel} : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 2) + count_ones_fuel fuel' (n / 2)
    end
  end.

(* Prove count_ones_helper_rel n n (count_ones_fuel n n) by induction on n *)

Lemma count_ones_helper_rel_correct :
  forall n,
  count_ones_helper_rel n n (count_ones_fuel n n).
Proof.
  induction n using nat_ind2; simpl.
  - constructor.
  - destruct n.
    + constructor.
    + apply cohr_step with (fuel' := n) (ones_tail := count_ones_fuel n (n / 2)).
      * reflexivity.
      * discriminate.
      * apply IHn.
Qed.

Lemma count_ones_rel_correct :
  forall n,
  count_ones_rel n (count_ones_fuel n n).
Proof.
  intros.
  apply cor_base.
  apply count_ones_helper_rel_correct.
Qed.

(* Boolean comparison rewritten using count_ones_fuel *)

Definition lt_custom_bool_dec (a b : nat) : bool :=
  let ones_a := count_ones_fuel a a in
  let ones_b := count_ones_fuel b b in
  if Nat.ltb ones_a ones_b then true
  else if Nat.eqb ones_a ones_b then Nat.ltb a b
  else false.

(* Equivalence of lt_custom_bool and lt_custom_bool_dec *)

Lemma lt_custom_bool_equiv :
  forall a b,
  lt_custom_bool a b <-> lt_custom_bool_dec a b = true.
Proof.
  intros a b.
  unfold lt_custom_bool, lt_custom_bool_dec.
  split; intros H.
  - destruct H as [ones_a [ones_b [Ha [Hb Hlt]]]].
    (* from count_ones_rel_correct ones_a = count_ones_fuel a a, etc *)
    replace ones_a with (count_ones_fuel a a) in Hlt.
    replace ones_b with (count_ones_fuel b b) in Hlt.
    + clear Ha Hb.
      destruct Hlt as [Hlt|[Heq Hlt2]].
      * apply Nat.ltb_lt in Hlt. now rewrite Nat.ltb_lt.
      * apply Nat.eqb_eq in Heq.
        rewrite Heq.
        apply Nat.ltb_lt in Hlt2.
        now rewrite Nat.ltb_lt.
    + inversion Ha; subst; rewrite <- count_ones_helper_rel_correct by reflexivity; reflexivity.
    + inversion Hb; subst; rewrite <- count_ones_helper_rel_correct by reflexivity; reflexivity.
  - simpl in H.
    destruct (Nat.ltb (count_ones_fuel a a) (count_ones_fuel b b)) eqn:Hltb.
    + exists (count_ones_fuel a a), (count_ones_fuel b b).
      repeat split; try apply count_ones_rel_correct.
      left. apply Nat.ltb_lt; assumption.
    + destruct (Nat.eqb (count_ones_fuel a a) (count_ones_fuel b b)) eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        exists (count_ones_fuel a a), (count_ones_fuel b b).
        repeat split; try apply count_ones_rel_correct.
        right; split; [assumption|].
        apply Nat.ltb_lt.
        destruct (Nat.ltb a b) eqn:Hlt.
        -- assumption.
        -- lia.
      * congruence.
Qed.

(* Tactic to solve lt_custom_bool goals with count_ones_fuel *)

Ltac solve_lt_custom_bool x y :=
  unfold lt_custom_bool;
  eexists (count_ones_fuel x x), (count_ones_fuel y y);
  repeat split; try apply count_ones_rel_correct;
  simpl;
  repeat match goal with
  | _ => progress rewrite Nat.ltb_lt || progress rewrite Nat.eqb_eq || progress simpl
  | |- ((?a <? ?b) = true) => apply Nat.ltb_lt; lia
  | |- (?a =? ?b) = true => apply Nat.eqb_eq; lia
  | |- _ \/ _ => left; reflexivity
  end.

(* Now prove insert_sorted_rel for inserts in test case *)

Example insert_3_in_4_list :
  insert_sorted_rel 3 [4] [3;4].
Proof.
  constructor 3.
  - unfold lt_custom_bool; intro H.
    destruct H as [oa [ob [Ha [Hb Hlt]]]].
    simpl in Hlt.
    destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
  - constructor 2.
    solve_lt_custom_bool 3 4.
Qed.

Example insert_4_in_23_list :
  insert_sorted_rel 4 [2;3] [2;4;3].
Proof.
  constructor 3.
  - unfold lt_custom_bool; intro H.
    destruct H as [oa [ob [Ha [Hb Hlt]]]].
    simpl in Hlt.
    destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
  - constructor 3.
    + unfold lt_custom_bool; intro H.
      destruct H as [oa [ob [Ha [Hb Hlt]]]].
      simpl in Hlt.
      destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
    + constructor 2.
      solve_lt_custom_bool 4 3.
Qed.

Example insert_2_in_14_list :
  insert_sorted_rel 2 [1;4] [1;2;4].
Proof.
  constructor 3.
  - unfold lt_custom_bool; intro H.
    destruct H as [oa [ob [Ha [Hb Hlt]]]].
    simpl in Hlt.
    destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
  - constructor 3.
    + unfold lt_custom_bool; intro H.
      destruct H as [oa [ob [Ha [Hb Hlt]]]].
      simpl in Hlt.
      destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
    + constructor 2.
      solve_lt_custom_bool 2 4.
Qed.

Example insert_1_in_nil :
  insert_sorted_rel 1 [] [1].
Proof.
  constructor.
Qed.

Example insert_5_in_1243_list :
  insert_sorted_rel 5 [1;2;4;3] [1;2;4;3;5].
Proof.
  constructor 3.
  - unfold lt_custom_bool; intro H.
    destruct H as [oa [ob [Ha [Hb Hlt]]]].
    simpl in Hlt.
    destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
  - constructor 3.
    + unfold lt_custom_bool; intro H.
      destruct H as [oa [ob [Ha [Hb Hlt]]]].
      simpl in Hlt.
      destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
    + constructor 3.
      * unfold lt_custom_bool; intro H.
        destruct H as [oa [ob [Ha [Hb Hlt]]]].
        simpl in Hlt.
        destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
      * constructor 3.
        -- unfold lt_custom_bool; intro H.
           destruct H as [oa [ob [Ha [Hb Hlt]]]].
           simpl in Hlt.
           destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
        -- constructor 2.
           solve_lt_custom_bool 5 3.
Qed.

(* Finally prove problem_116_spec for the test case *)

Example test_problem_116_spec :
  problem_116_spec [1;5;2;3;4] [1;2;4;3;5].
Proof.
  unfold problem_116_spec.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- constructor.
           constructor.
        -- insert_3_in_4_list.
      * constructor 3.
        -- unfold lt_custom_bool; intro H.
           destruct H as [oa [ob [Ha [Hb Hlt]]]].
           simpl in Hlt.
           destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
        -- constructor 3.
           ++ unfold lt_custom_bool; intro H.
              destruct H as [oa [ob [Ha [Hb Hlt]]]].
              simpl in Hlt.
              destruct Hlt as [Hlt|[Heq Hlt]]; simpl in *; lia.
           ++ constructor 2.
              solve_lt_custom_bool 2 3.
    + insert_5_in_1243_list.
  - constructor 3.
    + unfold lt_custom_bool; eexists _, _; repeat split; try apply count_ones_rel_correct; simpl; left; reflexivity.
Qed.

Qed.