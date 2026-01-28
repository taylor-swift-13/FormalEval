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

Example test_case : sorted_list_sum_spec ["poupular"; "iss"; "lizardpython"; "poupulworldar"; "is"; "popular"] ["is"; "poupular"; "lizardpython"].
Proof.
  unfold sorted_list_sum_spec.
  split.
  - intros s.
    split.
    + intros H.
      simpl in H.
      destruct H as [H_is | [H_poup | [H_liz | H_empty]]].
      * subst.
        split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- compute. reflexivity.
      * subst.
        split.
        -- simpl. left. reflexivity.
        -- compute. reflexivity.
      * subst.
        split.
        -- simpl. right. right. left. reflexivity.
        -- compute. reflexivity.
      * contradiction.
    + intros [H_in H_even].
      simpl in H_in.
      destruct H_in as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]].
      * subst. simpl. right. left. reflexivity.
      * subst. compute in H_even. discriminate H_even.
      * subst. simpl. right. right. left. reflexivity.
      * subst. compute in H_even. discriminate H_even.
      * subst. simpl. left. reflexivity.
      * subst. compute in H_even. discriminate H_even.
      * contradiction.
  - simpl.
    split.
    + left. compute. reflexivity.
    + split.
      * left. compute. reflexivity.
      * trivial.
Qed.