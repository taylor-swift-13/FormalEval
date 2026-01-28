Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition has_even_length (s : string) : bool :=
  Nat.even (String.length s).

Definition cmp_strings (s t : string) : comparison :=
  let len_s := String.length s in
  let len_t := String.length t in
  match Nat.compare len_s len_t with
  | Lt => Lt
  | Gt => Gt
  | Eq => String.compare s t
  end.

Fixpoint is_sorted_by (cmp : string -> string -> comparison) (l : list string) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: _) as tl => 
      (cmp x y = Lt \/ cmp x y = Eq) /\ is_sorted_by cmp tl
  end.

Definition is_permutation_of_filtered (original filtered : list string) : Prop :=
  forall s, In s filtered <-> (In s original /\ has_even_length s = true).

Definition sorted_list_sum_spec (lst : list string) (result : list string) : Prop :=
  (forall s, In s result <-> (In s lst /\ has_even_length s = true)) /\
  is_sorted_by cmp_strings result.

Example test_case : sorted_list_sum_spec ["dog"; "cat"; "bird"; "fish"; "lizard"; "fish"] ["bird"; "fish"; "fish"; "lizard"].
Proof.
  unfold sorted_list_sum_spec.
  split.
  - intros s.
    split.
    + intros H.
      repeat destruct H as [H|H]; subst; split; try (simpl; tauto); try (compute; reflexivity); try contradiction.
    + intros [H_in H_even].
      repeat destruct H_in as [H|H_in]; subst.
      * compute in H_even. discriminate.
      * compute in H_even. discriminate.
      * simpl; tauto.
      * simpl; tauto.
      * simpl; tauto.
      * simpl; tauto.
      * contradiction.
  - simpl.
    repeat split; compute; auto.
Qed.