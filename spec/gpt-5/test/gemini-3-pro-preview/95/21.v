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

(* Test Case: input = [{'2019': 'yeyar'}] *)
Definition d_test : Dict := [("2019", "yeyar")].

(* Proof for the Test Case *)
Example test_check_dict_case : check_dict_case_spec d_test false.
Proof.
  unfold check_dict_case_spec.
  split.
  - intros H. discriminate H.
  - intros [H_not_nil [H_lower | H_upper]].
    + (* Case: All keys are lower *)
      assert (H_in : In "2019" (keys d_test)).
      { unfold d_test, keys. simpl. left. reflexivity. }
      apply H_lower in H_in.
      destruct H_in as [s [H_key H_is_lower]].
      unfold KeyStr in H_key. subst s.
      simpl in H_is_lower.
      destruct H_is_lower as [H_char_lower _].
      unfold is_lower_char in H_char_lower. simpl in H_char_lower.
      destruct H_char_lower as [H_ge _].
      assert (H_lt : 50 < 97) by (repeat constructor).
      apply Nat.nle_gt in H_lt.
      contradiction.
    + (* Case: All keys are upper *)
      assert (H_in : In "2019" (keys d_test)).
      { unfold d_test, keys. simpl. left. reflexivity. }
      apply H_upper in H_in.
      destruct H_in as [s [H_key H_is_upper]].
      unfold KeyStr in H_key. subst s.
      simpl in H_is_upper.
      destruct H_is_upper as [H_char_upper _].
      unfold is_upper_char in H_char_upper. simpl in H_char_upper.
      destruct H_char_upper as [H_ge _].
      assert (H_lt : 50 < 65) by (repeat constructor).
      apply Nat.nle_gt in H_lt.
      contradiction.
Qed.