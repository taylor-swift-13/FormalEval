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

Example test_find_max : find_max_spec ["apple"; "orange"; "abanana"; "grape"; "ana"; "banana"; "riwi"; "pear"; "ana"] "orange".
Proof.
  unfold find_max_spec.
  split.

  - (* Prove "orange" is in the list *)
    simpl. right. left. reflexivity.

  - (* Prove "orange" satisfies the condition against all words *)
    intros w H_in.
    simpl in H_in.
    destruct H_in as [H_apple | [H_orange | [H_abanana | [H_grape | [H_ana1 | [H_banana | [H_riwi | [H_pear | [H_ana2 | H_empty]]]]]]]]].

    + (* Case: w = "apple" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: w = "orange" *)
      subst w.
      right.
      split.
      * reflexivity.
      * right. reflexivity.

    + (* Case: w = "abanana" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: w = "grape" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: w = "ana" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: w = "banana" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: w = "riwi" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: w = "pear" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: w = "ana" *)
      subst w.
      left.
      vm_compute.
      repeat constructor.

    + (* Case: empty list tail *)
      contradiction.
Qed.