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

(* Test Case: input = [{'p': 'pineapple', 'b': 'banana'}] *)
Definition d_test : Dict := [("p", "pineapple"); ("b", "banana")].

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
    + left. (* Keys "p" and "b" are lowercase *)
      intros k H_in.
      unfold d_test, keys in H_in.
      simpl in H_in.
      destruct H_in as [H_p | [H_b | H_false]].
      
      (* Case: k = "p" *)
      * subst k. exists "p".
        split.
        -- unfold KeyStr. reflexivity.
        -- simpl. split.
           ++ unfold is_lower_char. simpl. 
              (* Prove 97 <= 112 <= 122 *)
              split; repeat constructor.
           ++ exact I.
           
      (* Case: k = "b" *)
      * subst k. exists "b".
        split.
        -- unfold KeyStr. reflexivity.
        -- simpl. split.
           ++ unfold is_lower_char. simpl. 
              (* Prove 97 <= 98 <= 122 *)
              split; repeat constructor.
           ++ exact I.
           
      (* Case: End of list *)
      * contradiction.
      
  - intros _. reflexivity.
Qed.