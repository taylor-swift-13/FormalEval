Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* The function list_ascii_of_string is usually defined in String library as:
   Fixpoint list_ascii_of_string (s : string) : list ascii := ... *)

(* For this proof we only need to unfold it once to a list of ascii *)

Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

(* We define the explicit ascii lists corresponding to the input strings.
   This avoids pattern matching or destruct on In directly, preventing "No product" errors *)

Definition l0 := ["e"; "a"; "b"; "c"; "d"; "z"; "z"; "z"; "z"].
Definition l1 := ["d"; "d"; "d"; "z"; "z"; "z"; "z"; "z"; "z"; "z"; "d"; "d"; "e"; "d"; "d"; "a"; "b"; "c"].

(* We'll prove that the multiset of chars in these lists matches the membership predicate *)

Example problem_54_example :
  problem_54_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  unfold problem_54_spec, list_ascii_of_string.
  simpl.

  (* Replace lists by explicit lists *)
  change (list_ascii_of_string "eabcdzzzz") with l0.
  change (list_ascii_of_string "dddzzzzzzzddeddabc") with l1.

  split; intro _; intro c; split; intro Hin.

  - (* -> direction: c ∈ l0 -> c ∈ l1 *)
    destruct Hin as [Heq | Hin_rest].
    + subst c.
      (* "e" ∈ l1 *)
      simpl in *.
      right; right; right; right; right; right; right; right; right; right;
      right; right; left; reflexivity.
    + repeat (simpl in Hin_rest; destruct Hin_rest as [Heq | Hin_rest]).
      * subst c.
        (* "a" in l1 *)
        simpl.
        repeat (right; right; right; right; right; right; right; right; right; right;
                right; right).
        right; right; right; right; right; left; reflexivity.
      * destruct Hin_rest as [Heq | Hin_rest].
        -- subst c.
           (* "b" in l1 *)
           simpl.
           repeat (right; right; right; right; right; right; right; right; right; right;
                   right; right; right; right; right; left; reflexivity).
        -- destruct Hin_rest as [Heq | Hin_rest].
           ++ subst c.
              (* "c" in l1 *)
              simpl.
              repeat (right; right; right; right; right; right; right; right; right; right;
                      right; right; right; right; right; right; left; reflexivity).
           ++ destruct Hin_rest as [Heq | Hin_rest].
              ** subst c.
                 (* "d" in l1 *)
                 simpl.
                 left; reflexivity.
              ** destruct Hin_rest as [Heq | Hin_rest].
                 --- subst c.
                     (* "z" in l1 *)
                     simpl.
                     repeat (left || right); left; reflexivity.
                 --- inversion Hin_rest.
  - (* <- direction: c ∈ l1 -> c ∈ l0 *)
    simpl in Hin.
    repeat (destruct Hin as [Heq | Hin]; [subst c | ]).
    + (* c = "d" *)
      right; right; right; right; left; reflexivity.
    + + (* c = "z" *)
      right; right; right; right; right; left; reflexivity.
    + + (* c = "e" *)
      left; reflexivity.
    + + (* c = "a" *)
      right; left; reflexivity.
    + + (* c = "b" *)
      right; right; left; reflexivity.
    + + (* c = "c" *)
      right; right; right; left; reflexivity.
    + + inversion Hin.
  - (* trivial backward direction for b = true *)
    reflexivity.
Qed.