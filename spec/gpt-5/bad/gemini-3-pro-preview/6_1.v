Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Open Scope string_scope.
Open Scope Z_scope.
Import ListNotations.

(* --- Specification Definitions --- *)

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

(* --- Proof --- *)

(* Helper tactic to prove NoSpace for concrete strings *)
Ltac solve_nospace :=
  repeat (constructor; [ intro H; inversion H | ]); apply NoSpace_empty.

Example test_case_proof : 
  parse_nested_parens_spec "(()()) ((())) () ((())()())" [2%nat; 3%nat; 1%nat; 3%nat].
Proof.
  unfold parse_nested_parens_spec.
  (* Identify the split groups *)
  exists ["(()())"; "((()))"; "()"; "((())()())"].
  split.
  - (* Prove SplitNonEmptySpaceTokens *)
    unfold SplitNonEmptySpaceTokens.
    (* Identify the spaces: 0 before, 1 between each, 0 after *)
    exists [0; 1; 1; 1; 0]%nat.
    split.
    + (* Length check: 5 = S 4 *)
      reflexivity.
    + split.
      * (* Interior positive check for spaces *)
        unfold interior_positive_for_groups.
        exists 0%nat, 0%nat, [1; 1; 1]%nat.
        split.
        -- reflexivity.
        -- (* Prove 1 <= 1 for all elements in mid *)
           repeat constructor.
      * split.
        -- (* NonEmpty check *)
           repeat constructor; intro H; inversion H.
        -- split.
           ++ (* NoSpace check *)
              repeat constructor; try solve_nospace.
           ++ (* String reconstruction check *)
              simpl. reflexivity.
  - (* Prove depth calculation *)
    (* Use vm_compute to calculate the depths of the concrete strings *)
    vm_compute.
    reflexivity.
Qed.