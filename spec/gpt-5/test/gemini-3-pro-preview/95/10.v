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

(* Test Case: input = [{'firstName': 'John', 'LASTNAME': 'DOE', 'Age': 35, 'cItY': 'new york', 'Income': '$50,000'}] *)
Definition d_test : Dict := [
  ("firstName", "John");
  ("LASTNAME", "DOE");
  ("Age", "35");
  ("cItY", "new york");
  ("Income", "$50,000")
].

(* Proof for the Test Case *)
Example test_check_dict_case : check_dict_case_spec d_test false.
Proof.
  unfold check_dict_case_spec.
  split.
  - intros H. discriminate H.
  - intros [_ [H_all_lower | H_all_upper]].
    (* Case: All keys are lower *)
    + assert (H_in : In "LASTNAME" (keys d_test)).
      { unfold d_test, keys. simpl. right. left. reflexivity. }
      specialize (H_all_lower "LASTNAME" H_in).
      destruct H_all_lower as [s [H_eq H_is_lower]].
      unfold KeyStr in H_eq. subst s.
      simpl in H_is_lower. destruct H_is_lower as [H_char _].
      unfold is_lower_char in H_char. simpl in H_char.
      destruct H_char as [H_ge _].
      (* 'L' is 76. 97 <= 76 is false *)
      assert (H_lt: 76 < 97) by repeat constructor.
      apply Nat.nle_gt in H_lt. contradiction.
      
    (* Case: All keys are upper *)
    + assert (H_in : In "firstName" (keys d_test)).
      { unfold d_test, keys. simpl. left. reflexivity. }
      specialize (H_all_upper "firstName" H_in).
      destruct H_all_upper as [s [H_eq H_is_upper]].
      unfold KeyStr in H_eq. subst s.
      simpl in H_is_upper. destruct H_is_upper as [H_char _].
      unfold is_upper_char in H_char. simpl in H_char.
      destruct H_char as [_ H_le].
      (* 'f' is 102. 102 <= 90 is false *)
      assert (H_lt: 90 < 102) by repeat constructor.
      apply Nat.nle_gt in H_lt. contradiction.
Qed.