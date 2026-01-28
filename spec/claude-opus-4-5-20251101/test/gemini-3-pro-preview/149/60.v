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

Example test_case : sorted_list_sum_spec ["poupular"; "lizardpython"; "is"; ""; "popular"; ""] [""; ""; "is"; "poupular"; "lizardpython"].
Proof.
  unfold sorted_list_sum_spec.
  split.
  - (* Verify the filtering condition *)
    intros s.
    split.
    + (* Forward direction: In result -> In input /\ even length *)
      intros H.
      simpl in H.
      destruct H as [H | [H | [H | [H | [H | H]]]]].
      * (* Case s = "" (1st) *)
        subst.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "" (2nd) *)
        subst.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "is" *)
        subst.
        split.
        -- simpl. right. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "poupular" *)
        subst.
        split.
        -- simpl. left. reflexivity.
        -- compute. reflexivity.
      * (* Case s = "lizardpython" *)
        subst.
        split.
        -- simpl. right. left. reflexivity.
        -- compute. reflexivity.
      * (* Case Empty *)
        contradiction.
    + (* Backward direction: In input /\ even length -> In result *)
      intros [H_in H_even].
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | [H | [H | H]]]]]].
      * (* Case s = "poupular" *)
        subst. simpl. right. right. right. left. reflexivity.
      * (* Case s = "lizardpython" *)
        subst. simpl. right. right. right. right. left. reflexivity.
      * (* Case s = "is" *)
        subst. simpl. right. right. left. reflexivity.
      * (* Case s = "" (1st) *)
        subst. simpl. left. reflexivity.
      * (* Case s = "popular" *)
        subst.
        compute in H_even.
        discriminate H_even.
      * (* Case s = "" (2nd) *)
        subst. simpl. left. reflexivity.
      * (* Case Empty *)
        contradiction.
  - (* Verify the sorting condition *)
    simpl.
    split.
    + compute. right. reflexivity.
    + split.
      * compute. left. reflexivity.
      * split.
        -- compute. left. reflexivity.
        -- split.
           ++ compute. left. reflexivity.
           ++ trivial.
Qed.