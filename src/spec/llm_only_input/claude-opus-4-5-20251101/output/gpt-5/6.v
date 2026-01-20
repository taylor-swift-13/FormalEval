Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Open Scope string_scope.
Open Scope Z_scope.
Import ListNotations.

Definition ascii_eqb (a b : ascii) : bool :=
  if ascii_dec a b then true else false.

Fixpoint repeat_space (n : nat) : string :=
  match n with
  | O => EmptyString
  | S k => String " "%char (repeat_space k)
  end.

Inductive NoSpace : string -> Prop :=
| NoSpace_empty : NoSpace EmptyString
| NoSpace_cons : forall c s, c <> " "%char -> NoSpace s -> NoSpace (String c s).

Definition NonEmpty (s : string) : Prop := s <> EmptyString.

Fixpoint build_with_spaces (ks : list nat) (gs : list string) : string :=
  match gs with
  | [] =>
      match ks with
      | [k] => repeat_space k
      | _ => EmptyString
      end
  | g :: gs' =>
      match ks with
      | k :: ks' => repeat_space k ++ g ++ build_with_spaces ks' gs'
      | _ => EmptyString
      end
  end.

Definition interior_positive_for_groups (ks : list nat) (gs : list string) : Prop :=
  match gs with
  | [] => True
  | _ =>
      exists k0 kl mid,
        ks = k0 :: mid ++ [kl]
        /\ Forall (fun k => (1 <= k)%nat) mid
  end.

Definition SplitNonEmptySpaceTokens (s : string) (groups : list string) : Prop :=
  exists ks,
    length ks = S (length groups)
    /\ interior_positive_for_groups ks groups
    /\ Forall NonEmpty groups
    /\ Forall NoSpace groups
    /\ s = build_with_spaces ks groups.

Fixpoint count_depth_z_aux (s : string) (cnt mx : Z) : Z :=
  match s with
  | EmptyString => mx
  | String c s' =>
      let cnt' :=
        if ascii_eqb c "(" %char then cnt + 1
        else if ascii_eqb c ")" %char then cnt - 1
        else cnt in
      let mx' := Z.max mx cnt' in
      count_depth_z_aux s' cnt' mx'
  end.

Definition count_depth (s : string) : nat :=
  Z.to_nat (count_depth_z_aux s 0 0).

Definition parse_nested_parens_spec (paren_string : string) (depths : list nat) : Prop :=
  exists groups,
    SplitNonEmptySpaceTokens paren_string groups
    /\ depths = List.map count_depth groups.

Lemma NoSpace_group1 : NoSpace "(()())".
Proof.
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_empty.
Qed.

Lemma NoSpace_group2 : NoSpace "((()))".
Proof.
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_empty.
Qed.

Lemma NoSpace_group3 : NoSpace "()".
Proof.
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_empty.
Qed.

Lemma NoSpace_group4 : NoSpace "((())()())".
Proof.
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_cons. { intro H; discriminate H. }
  apply NoSpace_empty.
Qed.

Lemma NonEmpty_group1 : NonEmpty "(()())".
Proof. unfold NonEmpty. discriminate. Qed.

Lemma NonEmpty_group2 : NonEmpty "((()))".
Proof. unfold NonEmpty. discriminate. Qed.

Lemma NonEmpty_group3 : NonEmpty "()".
Proof. unfold NonEmpty. discriminate. Qed.

Lemma NonEmpty_group4 : NonEmpty "((())()())".
Proof. unfold NonEmpty. discriminate. Qed.

Example parse_nested_parens_test :
  parse_nested_parens_spec "(()()) ((())) () ((())()())" [2%nat; 3%nat; 1%nat; 3%nat].
Proof.
  unfold parse_nested_parens_spec.
  exists ["(()())"; "((()))"; "()"; "((())()())"].
  split.
  - unfold SplitNonEmptySpaceTokens.
    exists [0%nat; 1%nat; 1%nat; 1%nat; 0%nat].
    split.
    + simpl. reflexivity.
    + split.
      * unfold interior_positive_for_groups.
        exists 0%nat, 0%nat, [1%nat; 1%nat; 1%nat].
        split.
        -- reflexivity.
        -- constructor. { lia. }
           constructor. { lia. }
           constructor. { lia. }
           constructor.
      * split.
        -- constructor. { exact NonEmpty_group1. }
           constructor. { exact NonEmpty_group2. }
           constructor. { exact NonEmpty_group3. }
           constructor. { exact NonEmpty_group4. }
           constructor.
        -- split.
           ++ constructor. { exact NoSpace_group1. }
              constructor. { exact NoSpace_group2. }
              constructor. { exact NoSpace_group3. }
              constructor. { exact NoSpace_group4. }
              constructor.
           ++ simpl. reflexivity.
  - simpl.
    unfold count_depth.
    simpl.
    reflexivity.
Qed.