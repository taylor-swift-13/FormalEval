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

Example test_find_max : find_max_spec ["apple"; "orange"; "abanabna"; "grape"; "ana"; "banana"; "kiwi"; "pear"] "orange".
Proof.
  unfold find_max_spec.
  split.
  - (* Prove "orange" is in the list *)
    simpl. right. left. reflexivity.
  - (* Prove property for all words *)
    intros w H_in.
    simpl in H_in.
    destruct H_in as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
    + (* apple *)
      subst. left. vm_compute. repeat constructor.
    + (* orange *)
      subst. right. split.
      * reflexivity.
      * right. reflexivity.
    + (* abanabna *)
      subst. left. vm_compute. repeat constructor.
    + (* grape *)
      subst. left. vm_compute. repeat constructor.
    + (* ana *)
      subst. left. vm_compute. repeat constructor.
    + (* banana *)
      subst. left. vm_compute. repeat constructor.
    + (* kiwi *)
      subst. left. vm_compute. repeat constructor.
    + (* pear *)
      subst. left. vm_compute. repeat constructor.
    + (* End of list *)
      contradiction.
Qed.