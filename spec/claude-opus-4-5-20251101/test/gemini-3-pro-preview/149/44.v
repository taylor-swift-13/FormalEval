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

Example test_case : sorted_list_sum_spec ["aaaa"; "bb"; "cccc"; "ccccc"; "cccc"; "ddd"] ["bb"; "aaaa"; "cccc"; "cccc"].
Proof.
  unfold sorted_list_sum_spec.
  split.
  - (* Verify the filtering condition *)
    intros s.
    split.
    + (* Forward direction: In result -> In input /\ even length *)
      intros H.
      simpl in H.
      destruct H as [H_bb | [H_aaaa | [H_cccc1 | [H_cccc2 | H_empty]]]].
      * (* s = "bb" *)
        subst. split.
        -- simpl. right. left. reflexivity.
        -- compute. reflexivity.
      * (* s = "aaaa" *)
        subst. split.
        -- simpl. left. reflexivity.
        -- compute. reflexivity.
      * (* s = "cccc" *)
        subst. split.
        -- simpl. right. right. left. reflexivity.
        -- compute. reflexivity.
      * (* s = "cccc" *)
        subst. split.
        -- simpl. right. right. left. reflexivity.
        -- compute. reflexivity.
      * contradiction.
    + (* Backward direction: In input /\ even length -> In result *)
      intros [H_in H_even].
      simpl in H_in.
      destruct H_in as [H_aaaa | [H_bb | [H_cccc1 | [H_ccccc | [H_cccc2 | [H_ddd | H_empty]]]]]].
      * (* s = "aaaa" *)
        subst. simpl. right. left. reflexivity.
      * (* s = "bb" *)
        subst. simpl. left. reflexivity.
      * (* s = "cccc" *)
        subst. simpl. right. right. left. reflexivity.
      * (* s = "ccccc" *)
        subst. compute in H_even. discriminate H_even.
      * (* s = "cccc" *)
        subst. simpl. right. right. left. reflexivity.
      * (* s = "ddd" *)
        subst. compute in H_even. discriminate H_even.
      * contradiction.
  - (* Verify the sorting condition *)
    simpl.
    repeat split.
    + left. compute. reflexivity.
    + left. compute. reflexivity.
    + right. compute. reflexivity.
Qed.