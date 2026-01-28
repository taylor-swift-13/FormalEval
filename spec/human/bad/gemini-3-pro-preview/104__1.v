Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.

Import ListNotations.

(* Definitions provided in the specification *)
Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Inductive all_digits_odd_list_rel : list nat -> Prop :=
  | adolr_nil : all_digits_odd_list_rel []
  | adolr_cons : forall h t,
      is_odd_digit h ->
      all_digits_odd_list_rel t ->
      all_digits_odd_list_rel (h :: t).

Inductive nat_to_digits_rel : nat -> list nat -> Prop :=
  | ntdr_zero : nat_to_digits_rel 0 []
  | ntdr_step : forall n d rest,
      n > 0 ->
      d = n mod 10 ->
      nat_to_digits_rel (n / 10) rest ->
      nat_to_digits_rel n (d :: rest).

Inductive has_only_odd_digits_rel : nat -> Prop :=
  | hodd_base : forall n digits,
      n > 0 ->
      nat_to_digits_rel n digits ->
      all_digits_odd_list_rel digits ->
      has_only_odd_digits_rel n.

Inductive filter_odd_digits_rel : list nat -> list nat -> Prop :=
  | fodr_nil : filter_odd_digits_rel [] []
  | fodr_keep : forall h t result,
      has_only_odd_digits_rel h ->
      filter_odd_digits_rel t result ->
      filter_odd_digits_rel (h :: t) (h :: result)
  | fodr_drop : forall h t result,
      ~ has_only_odd_digits_rel h ->
      filter_odd_digits_rel t result ->
      filter_odd_digits_rel (h :: t) result.

Inductive insert_sorted_rel : nat -> list nat -> list nat -> Prop :=
  | isr_nil : forall x, insert_sorted_rel x [] [x]
  | isr_insert : forall x h t,
      (x <= h)%nat ->
      insert_sorted_rel x (h :: t) (x :: h :: t)
  | isr_skip : forall x h t result,
      (x > h)%nat ->
      insert_sorted_rel x t result ->
      insert_sorted_rel x (h :: t) (h :: result).

Inductive sort_list_rel : list nat -> list nat -> Prop :=
  | slr_nil : sort_list_rel [] []
  | slr_cons : forall h t sorted_tail result,
      sort_list_rel t sorted_tail ->
      insert_sorted_rel h sorted_tail result ->
      sort_list_rel (h :: t) result.

Definition problem_104_pre (x : list nat) : Prop := Forall (fun n => n > 0) x.

Definition problem_104_spec (x y : list nat) : Prop :=
  (forall n, In n x -> n > 0) /\
  exists filtered,
    filter_odd_digits_rel x filtered /\
    sort_list_rel filtered y.

(* Proof for the test case *)
Example unique_digits_test_case : problem_104_spec [15; 33; 1422; 1] [1; 15; 33].
Proof.
  unfold problem_104_spec.
  split.
  { (* Part 1: Precondition check *)
    intros n H.
    simpl in H.
    repeat destruct H as [<- | H]; try lia.
    contradiction.
  }
  { (* Part 2: Existence of filtered and sorted list *)
    exists [15; 33; 1].
    split.
    { (* Sub-proof: Filtering *)
      apply fodr_keep.
      { (* Case 15: Keep *)
        econstructor. lia.
        econstructor. lia. reflexivity.
        econstructor. lia. reflexivity.
        constructor.
        repeat constructor.
      }
      apply fodr_keep.
      { (* Case 33: Keep *)
        econstructor. lia.
        econstructor. lia. reflexivity.
        econstructor. lia. reflexivity.
        constructor.
        repeat constructor.
      }
      apply fodr_drop.
      { (* Case 1422: Drop *)
        intro H.
        inversion H as [n0 digits0 Hn0 Hdigits0 Hodd0]. subst.
        (* Deconstruct digits of 1422 *)
        (* 1422 mod 10 = 2, 1422 / 10 = 142 *)
        replace (1422 mod 10) with 2 in Hdigits0 by lia.
        replace (1422 / 10) with 142 in Hdigits0 by lia.
        inversion Hdigits0 as [|n1 d1 rest1 Hn1 Hd1 Hrest1]. subst.
        
        (* 142 mod 10 = 2, 142 / 10 = 14 *)
        replace (142 mod 10) with 2 in Hrest1 by lia.
        replace (142 / 10) with 14 in Hrest1 by lia.
        inversion Hrest1 as [|n2 d2 rest2 Hn2 Hd2 Hrest2]. subst.
        
        (* 14 mod 10 = 4, 14 / 10 = 1 *)
        replace (14 mod 10) with 4 in Hrest2 by lia.
        replace (14 / 10) with 1 in Hrest2 by lia.
        inversion Hrest2 as [|n3 d3 rest3 Hn3 Hd3 Hrest3]. subst.
        
        (* 1 mod 10 = 1, 1 / 10 = 0 *)
        replace (1 mod 10) with 1 in Hrest3 by lia.
        replace (1 / 10) with 0 in Hrest3 by lia.
        inversion Hrest3 as [|n4 d4 rest4 Hn4 Hd4 Hrest4]. subst.
        
        inversion Hrest4. subst.
        
        (* Check if digits are odd. Head is 2. *)
        inversion Hodd0 as [|h t Hhead Htail]. subst.
        unfold is_odd_digit in Hhead. lia.
      }
      apply fodr_keep.
      { (* Case 1: Keep *)
        econstructor. lia.
        econstructor. lia. reflexivity.
        constructor.
        repeat constructor.
      }
      apply fodr_nil.
    }
    { (* Sub-proof: Sorting [15; 33; 1] -> [1; 15; 33] *)
      eapply slr_cons.
      { (* Sort tail [33; 1] -> [1; 33] *)
        eapply slr_cons.
        { (* Sort tail [1] -> [1] *)
          eapply slr_cons.
          { apply slr_nil. }
          { apply isr_nil. }
        }
        { (* Insert 33 into [1] -> [1; 33] *)
          apply isr_skip. lia.
          apply isr_nil.
        }
      }
      { (* Insert 15 into [1; 33] -> [1; 15; 33] *)
        apply isr_skip. lia.
        apply isr_insert. lia.
      }
    }
  }
Qed.