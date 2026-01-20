Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.
Open Scope string_scope.

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

Example test_case_proof : sorted_list_sum_spec ["aa"; "a"; "aaa"] ["aa"].
Proof.
  unfold sorted_list_sum_spec.
  split; [| split].
  
  - (* Part 1: Preservation of even length strings *)
    intros s Heven.
    simpl.
    destruct (string_dec s "aa") as [E_aa | N_aa].
    + (* Case s = "aa" *)
      rewrite E_aa.
      (* Evaluate count on input list for "aa" *)
      destruct (string_dec "aa" "aa") as [_ | False_aa]; [| contradiction].
      destruct (string_dec "aa" "a") as [E_a | _].
      * inversion E_a.
      * destruct (string_dec "aa" "aaa") as [E_aaa | _].
        -- inversion E_aaa.
        -- reflexivity.
    + (* Case s <> "aa" *)
      (* Left side is 0, check Right side *)
      destruct (string_dec s "a") as [E_a | N_a].
      * (* s = "a" *)
        subst s.
        unfold even_length in Heven. simpl in Heven.
        destruct Heven as [k Hk].
        (* length "a" is 1, which is not even *)
        lia.
      * destruct (string_dec s "aaa") as [E_aaa | N_aaa].
        -- (* s = "aaa" *)
           subst s.
           unfold even_length in Heven. simpl in Heven.
           destruct Heven as [k Hk].
           (* length "aaa" is 3, which is not even *)
           lia.
        -- (* s is not "aa", "a", or "aaa" *)
           reflexivity.

  - (* Part 2: Removal of odd length strings *)
    intros s Hodd.
    simpl.
    destruct (string_dec s "aa") as [E_aa | N_aa].
    + (* s = "aa" *)
      subst s.
      (* "aa" has length 2, which is even, contradicting Hodd *)
      exfalso. apply Hodd.
      exists 1. simpl. reflexivity.
    + (* s <> "aa" *)
      reflexivity.

  - (* Part 3: Sortedness *)
    repeat constructor.
Qed.