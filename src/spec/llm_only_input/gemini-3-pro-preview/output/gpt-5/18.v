Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Local Open Scope string_scope.

Fixpoint drop (n : nat) (s : string) : string :=
  match n, s with
  | 0, _ => s
  | S n', EmptyString => EmptyString
  | S n', String _ s' => drop n' s'
  end.

Fixpoint is_prefixb (t u : string) : bool :=
  match t, u with
  | EmptyString, _ => true
  | String ct rt, String cu ru =>
      if ascii_dec ct cu then is_prefixb rt ru else false
  | String _ _, EmptyString => false
  end.

Definition how_many_times_spec (s substring : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => is_prefixb substring (drop i s))
                                 (List.seq 0 (String.length s))).

Example test_case_empty_string_x : how_many_times_spec "" "x" 0.
Proof.
  (* Unfold the specification definition *)
  unfold how_many_times_spec.
  
  (* Simplify the expression.
     1. String.length "" evaluates to 0.
     2. List.seq 0 0 evaluates to [].
     3. List.filter over an empty list evaluates to [].
     4. List.length [] evaluates to 0.
  *)
  simpl.
  
  (* The goal becomes 0 = 0, which is reflexively true *)
  reflexivity.
Qed.