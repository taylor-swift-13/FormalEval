Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope char_scope.

Definition three_consecutive_distinct (s : list ascii) (i : nat) : Prop :=
  match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
  | Some c1, Some c2, Some c3 => c1 <> c2 /\ c1 <> c3 /\ c2 <> c3
  | _, _, _ => False
  end.

Definition is_happy_spec (s : list ascii) (result : bool) : Prop :=
  (result = true <->
    (length s >= 3 /\
     forall i, i + 2 < length s -> three_consecutive_distinct s i)) /\
  (result = false <->
    (length s < 3 \/
     exists i, i + 2 < length s /\
       match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
       | Some c1, Some c2, Some c3 => c1 = c2 \/ c1 = c3 \/ c2 = c3
       | _, _, _ => False
       end)).

Example test_happy_case : is_happy_spec ["c"; "a"; "b"; "c"; "a"; "b"; "c"] true.
Proof.
  unfold is_happy_spec.
  split.
  - (* Case: result = true <-> ... *)
    split; intro H.
    + (* Left to Right: true = true -> ... *)
      split.
      * (* length >= 3 *)
        simpl. lia.
      * (* forall i ... *)
        intros i Hi.
        simpl in Hi.
        do 5 (destruct i; [
          unfold three_consecutive_distinct; simpl;
          repeat split; discriminate
        | ]).
        lia.
    + (* Right to Left: ... -> true = true *)
      reflexivity.
  - (* Case: result = false <-> ... *)
    split; intro H.
    + (* Left to Right: true = false -> ... *)
      discriminate H.
    + (* Right to Left: ... -> true = false *)
      destruct H as [Hlen | [i [Hi Hmatch]]].
      * (* length < 3 *)
        simpl in Hlen. lia.
      * (* exists i ... *)
        simpl in Hi.
        do 5 (destruct i; [
          simpl in Hmatch;
          destruct Hmatch as [Eq | [Eq | Eq]]; discriminate Eq
        | ]).
        lia.
Qed.