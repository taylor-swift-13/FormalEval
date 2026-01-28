Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.

Import ListNotations.
Open Scope string_scope.

(* Definitions *)

Fixpoint count (x : string) (l : list string) : nat :=
  match l with
  | [] => 0
  | y :: ys => if string_dec x y then S (count x ys) else count x ys
  end.

Definition ascii_lt (a b : ascii) : Prop :=
  nat_of_ascii a < nat_of_ascii b.

Fixpoint string_lex_lt (s t : string) : Prop :=
  match s, t with
  | EmptyString, EmptyString => False
  | EmptyString, String _ _ => True
  | String _ _, EmptyString => False
  | String a s', String b t' =>
      ascii_lt a b \/ (a = b /\ string_lex_lt s' t')
  end.

Definition string_lex_le (s t : string) : Prop :=
  s = t \/ string_lex_lt s t.

Definition even_length (s : string) : Prop :=
  exists k : nat, String.length s = 2 * k.

Definition orderR (s t : string) : Prop :=
  String.length s < String.length t \/
  (String.length s = String.length t /\ string_lex_le s t).

Definition sorted_list_sum_spec (lst res : list string) : Prop :=
  (forall s : string, even_length s -> count s res = count s lst) /\
  (forall s : string, ~ even_length s -> count s res = 0) /\
  Sorted orderR res.

(* Proof *)

Example test_sorted_list_sum: sorted_list_sum_spec ["aa"; "a"; "aaa"] ["aa"].
Proof.
  unfold sorted_list_sum_spec.
  repeat split.
  
  (* Part 1: Verify counts for even-length strings *)
  - intros s [k Hk].
    simpl.
    destruct (string_dec s "aa") as [H_aa | H_not_aa].
    + (* s = "aa" *)
      subst. reflexivity.
    + (* s <> "aa" *)
      destruct (string_dec s "a") as [H_a | H_not_a].
      * (* s = "a" *)
        subst. simpl in Hk.
        (* length "a" is 1. 1 = 2 * k *)
        destruct k.
        -- (* k = 0 -> 1 = 0 *) discriminate Hk.
        -- (* k >= 1 -> 1 = 2 + ... *) 
           simpl in Hk. discriminate Hk.
      * (* s <> "a" *)
        destruct (string_dec s "aaa") as [H_aaa | H_not_aaa].
        -- (* s = "aaa" *)
           subst. simpl in Hk.
           (* length "aaa" is 3. 3 = 2 * k *)
           destruct k.
           ++ (* k = 0 -> 3 = 0 *) discriminate Hk.
           ++ simpl in Hk. destruct k.
              ** (* k = 1 -> 3 = 2 *) discriminate Hk.
              ** (* k >= 2 -> 3 = 4 + ... *)
                 simpl in Hk. discriminate Hk.
        -- (* s <> "aaa" *)
           reflexivity.

  (* Part 2: Verify counts for non-even-length strings in result *)
  - intros s H_not_even.
    simpl.
    destruct (string_dec s "aa") as [H_aa | H_not_aa].
    + (* s = "aa" *)
      subst. exfalso. apply H_not_even.
      (* length "aa" is 2. 2 = 2 * 1 *)
      exists 1. simpl. reflexivity.
    + (* s <> "aa" *)
      reflexivity.

  (* Part 3: Verify result is Sorted *)
  - apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
Qed.