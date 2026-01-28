Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* Helper function to convert string to list of characters *)
Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_of_string s'
  end.

(* Helper function to count unique characters in a string *)
Definition count_unique (s : string) : nat :=
  length (nodup ascii_dec (list_of_string s)).

(* Helper predicate for strict lexicographical order *)
Fixpoint string_lt (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, EmptyString => False
  | EmptyString, String _ _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      (nat_of_ascii c1 < nat_of_ascii c2)%nat \/
      (nat_of_ascii c1 = nat_of_ascii c2 /\ string_lt s1' s2')
  end.

Definition find_max_spec (words : list string) (res : string) : Prop :=
  match words with
  | [] => res = ""
  | _ =>
      In res words /\
      (forall w, In w words ->
         (count_unique w < count_unique res)%nat \/
         (count_unique w = count_unique res /\ (string_lt res w \/ res = w)))
  end.

Example test_find_max : find_max_spec ["r"; "tac"; "act"] "act".
Proof.
  (* Unfold the specification definition *)
  unfold find_max_spec.
  split.
  
  - (* Part 1: Prove "act" is in the list *)
    simpl. right. right. left. reflexivity.

  - (* Part 2: Prove "act" satisfies the condition against all words *)
    intros w H_in.
    simpl in H_in.
    destruct H_in as [H_r | [H_tac | [H_act | H_empty]]].
    
    + (* Case: w = "r" *)
      subst w.
      left.
      (* count_unique "r" = 1, count_unique "act" = 3 *)
      vm_compute.
      repeat constructor.

    + (* Case: w = "tac" *)
      subst w.
      right.
      split.
      * (* count_unique "tac" = 3, count_unique "act" = 3 *)
        vm_compute. reflexivity.
      * (* string_lt "act" "tac" *)
        simpl. left.
        vm_compute.
        repeat constructor.

    + (* Case: w = "act" *)
      subst w.
      right.
      split.
      * reflexivity.
      * right. reflexivity.

    + (* Case: empty list tail *)
      contradiction.
Qed.