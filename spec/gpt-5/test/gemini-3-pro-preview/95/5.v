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

(* Test Case: input = [{'STATE': 'NC', 'ZIP': '12345'}] *)
Definition d_test : Dict := [("STATE", "NC"); ("ZIP", "12345")].

(* Proof for the Test Case *)
Example test_check_dict_case : check_dict_case_spec d_test true.
Proof.
  unfold check_dict_case_spec.
  split.
  - intros _.
    split.
    (* Part 1: keys d <> nil *)
    + unfold d_test, keys. simpl. discriminate.
    
    (* Part 2: All keys are lower or All keys are upper *)
    + right. (* Keys "STATE" and "ZIP" are uppercase *)
      intros k H_in.
      unfold d_test, keys in H_in.
      simpl in H_in.
      destruct H_in as [H_state | [H_zip | H_false]].
      
      (* Case: k = "STATE" *)
      * subst k. exists "STATE".
        split.
        -- unfold KeyStr. reflexivity.
        -- simpl. 
           repeat (split; [ unfold is_upper_char; simpl; split; repeat constructor | ]).
           exact I.
           
      (* Case: k = "ZIP" *)
      * subst k. exists "ZIP".
        split.
        -- unfold KeyStr. reflexivity.
        -- simpl.
           repeat (split; [ unfold is_upper_char; simpl; split; repeat constructor | ]).
           exact I.
           
      (* Case: End of list *)
      * contradiction.
      
  - intros _. reflexivity.
Qed.