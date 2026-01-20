Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
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

(* Compute count_unique for the test strings to verify values *)
Eval compute in count_unique "name".
Eval compute in count_unique "of".
Eval compute in count_unique "string".

(* Main example *)
Example test_find_max : find_max_spec ["name"; "of"; "string"] "string".
Proof.
  unfold find_max_spec.
  split.
  - (* "string" is in the list *)
    simpl. right. right. left. reflexivity.
  - (* For all words in the list, the condition holds *)
    intros w Hw.
    simpl in Hw.
    destruct Hw as [Hw | [Hw | [Hw | Hw]]].
    + (* w = "name" *)
      subst w.
      left.
      unfold count_unique. simpl.
      (* count_unique "name" = 4, count_unique "string" = 6 *)
      (* Need to show 4 < 6 *)
      auto.
    + (* w = "of" *)
      subst w.
      left.
      unfold count_unique. simpl.
      (* count_unique "of" = 2, count_unique "string" = 6 *)
      (* Need to show 2 < 6 *)
      auto.
    + (* w = "string" *)
      subst w.
      right.
      split.
      * reflexivity.
      * right. reflexivity.
    + (* contradiction: Hw is False *)
      destruct Hw.
Qed.