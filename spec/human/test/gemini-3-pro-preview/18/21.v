Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import Lia.
Open Scope string_scope.

(* Definition of match_at as per specification *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

(* Precondition (True as default) *)
Definition problem_18_pre (input substring : string) : Prop := True.

(* Specification definition *)
Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (* All indices in the list are valid matches *)
    (forall i, In i indices -> match_at i input substring) /\
    (* All valid matches are in the list *)
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    (* Output is the count of matches *)
    output = List.length indices.

(* Test case: input = "abababab", substring = "fox", output = 0 *)
Example test_problem_18_abababab_fox : problem_18_spec "abababab" "fox" 0.
Proof.
  unfold problem_18_spec.
  exists [].
  split.
  - apply NoDup_nil.
  - split.
    + intros i H. inversion H.
    + split.
      * intros i Hbound Hmatch.
        destruct Hmatch as [_ [_ Hget]].
        (* Check the first character: "fox" starts with 'f', "abababab" has only 'a', 'b' *)
        specialize (Hget 0).
        assert (Hlen : 0 < String.length "fox") by (simpl; lia).
        specialize (Hget Hlen).
        replace (i + 0) with i in Hget by lia.
        simpl in Hget.
        (* Bound is i + 3 <= 8, so i <= 5. We check cases 0 to 5. *)
        do 6 (destruct i; [ simpl in Hget; discriminate | ]).
        (* For i >= 6, the length bound is violated *)
        simpl in Hbound.
        lia.
      * simpl. reflexivity.
Qed.