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

Example test_sorted_list_sum : sorted_list_sum_spec ["apple"; "orange"; "banana"; "grapefruit"] ["banana"; "orange"; "grapefruit"].
Proof.
  unfold sorted_list_sum_spec.
  split.
  - intro s.
    split.
    + intro H.
      simpl in H.
      destruct H as [H | [H | [H | H]]].
      * subst s.
        split.
        -- simpl. right. right. left. reflexivity.
        -- unfold has_even_length. simpl. reflexivity.
      * subst s.
        split.
        -- simpl. right. left. reflexivity.
        -- unfold has_even_length. simpl. reflexivity.
      * subst s.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- unfold has_even_length. simpl. reflexivity.
      * contradiction.
    + intros [H1 H2].
      simpl in H1.
      destruct H1 as [H1 | [H1 | [H1 | [H1 | H1]]]].
      * subst s. unfold has_even_length in H2. simpl in H2. discriminate.
      * subst s. simpl. right. left. reflexivity.
      * subst s. simpl. left. reflexivity.
      * subst s. simpl. right. right. left. reflexivity.
      * contradiction.
  - simpl.
    split.
    + left. unfold cmp_strings. simpl. reflexivity.
    + split.
      * left. unfold cmp_strings. simpl. reflexivity.
      * trivial.
Qed.