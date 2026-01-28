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

(* Test Case: input = [{'8': 'banana'}] *)
Definition d_test : Dict := [("8", "banana")].

(* Proof for the Test Case *)
Example test_check_dict_case : check_dict_case_spec d_test false.
Proof.
  unfold check_dict_case_spec.
  split.
  - intros H. discriminate.
  - intros [H_not_nil [H_lower | H_upper]].
    + (* Case: All keys are lower *)
      assert (H_in : In "8" (keys d_test)).
      { unfold d_test, keys. simpl. left. reflexivity. }
      specialize (H_lower "8" H_in).
      destruct H_lower as [s [H_k H_l]].
      unfold KeyStr in H_k. subst s.
      simpl in H_l. destruct H_l as [H_char _].
      unfold is_lower_char in H_char. simpl in H_char.
      destruct H_char as [H_ge _].
      apply Nat.leb_le in H_ge. simpl in H_ge. discriminate.
    + (* Case: All keys are upper *)
      assert (H_in : In "8" (keys d_test)).
      { unfold d_test, keys. simpl. left. reflexivity. }
      specialize (H_upper "8" H_in).
      destruct H_upper as [s [H_k H_u]].
      unfold KeyStr in H_k. subst s.
      simpl in H_u. destruct H_u as [H_char _].
      unfold is_upper_char in H_char. simpl in H_char.
      destruct H_char as [H_ge _].
      apply Nat.leb_le in H_ge. simpl in H_ge. discriminate.
Qed.