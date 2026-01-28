Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

Import ListNotations.
Open Scope string_scope.

(* Concrete Implementation of the Abstract Parameters *)
Definition Key := string.
Definition Dict := list (string * string).

Definition keys (d : Dict) : list Key := map fst d.

Definition KeyStr (k : Key) (s : string) : Prop := k = s.

(* Helper predicates for character case *)
Definition is_lower_char (a : ascii) : Prop :=
  let n := nat_of_ascii a in (97 <= n /\ n <= 122).

Definition is_upper_char (a : ascii) : Prop :=
  let n := nat_of_ascii a in (65 <= n /\ n <= 90).

(* Recursive predicates for string case *)
Fixpoint IsLower (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c s' => is_lower_char c /\ IsLower s'
  end.

Fixpoint IsUpper (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c s' => is_upper_char c /\ IsUpper s'
  end.

(* Specification Definition *)
Definition check_dict_case_spec (d : Dict) (res : bool) : Prop :=
  res = true <->
  keys d <> nil /\
  ( (forall k, In k (keys d) -> exists s, KeyStr k s /\ IsLower s) \/
    (forall k, In k (keys d) -> exists s, KeyStr k s /\ IsUpper s) ).

(* Test Case: input = [{'p': 'pineapple', 'A': 'banana', 'B': 'banana'}] *)
Definition d_test : Dict := [("p", "pineapple"); ("A", "banana"); ("B", "banana")].

(* Proof for the Test Case *)
Example test_check_dict_case : check_dict_case_spec d_test false.
Proof.
  unfold check_dict_case_spec.
  split.
  - intros H. discriminate H.
  - intros [H_not_nil H_or].
    destruct H_or as [H_all_lower | H_all_upper].
    + (* Case: All keys are lower. Contradiction with "A" *)
      assert (H_in : In "A" (keys d_test)).
      { unfold d_test, keys. simpl. right. left. reflexivity. }
      apply H_all_lower in H_in.
      destruct H_in as [s [H_eq H_lower]].
      unfold KeyStr in H_eq. subst s.
      simpl in H_lower. destruct H_lower as [H_char _].
      unfold is_lower_char in H_char. simpl in H_char.
      destruct H_char as [H_ge _].
      (* 97 <= 65 is false *)
      assert (H_contra : 65 < 97) by repeat constructor.
      apply Nat.lt_nge in H_contra.
      contradiction.
    + (* Case: All keys are upper. Contradiction with "p" *)
      assert (H_in : In "p" (keys d_test)).
      { unfold d_test, keys. simpl. left. reflexivity. }
      apply H_all_upper in H_in.
      destruct H_in as [s [H_eq H_upper]].
      unfold KeyStr in H_eq. subst s.
      simpl in H_upper. destruct H_upper as [H_char _].
      unfold is_upper_char in H_char. simpl in H_char.
      destruct H_char as [_ H_le].
      (* 112 <= 90 is false *)
      assert (H_contra : 90 < 112) by repeat constructor.
      apply Nat.lt_nge in H_contra.
      contradiction.
Qed.